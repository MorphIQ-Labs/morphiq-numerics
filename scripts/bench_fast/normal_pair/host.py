"""Native build and scheduling boundary for the normal-pair benchmark."""
import ctypes as ct
import os
from pathlib import Path
import platform
import subprocess


def configuration():
    identity = platform.system(), platform.machine()
    if identity == ("Linux", "x86_64"):
        return dict(name="x86-linux", suffix="so", rustflags="-C target-cpu=x86-64-v3",
                    cflags=["-march=x86-64-v3", "-shared", "-fPIC"],
                    interpretation="Native x86-64-v3 Linux; pinned CPU, observed host conditions.")
    if identity == ("Darwin", "arm64"):
        return dict(name="arm-macos", suffix="dylib", rustflags="-C target-cpu=apple-m1",
                    cflags=["-mcpu=apple-m1", "-dynamiclib"],
                    interpretation="Native Apple Silicon macOS; USER_INITIATED QoS, no CPU affinity or frequency lock. Core migration and host contention remain observable limitations.")
    raise RuntimeError(f"Unsupported native host {identity}; use x86-64 Linux or Apple Silicon macOS")


def product_path(prepared):
    return prepared / f'target/release/libnormal_pair_screen.{configuration()["suffix"]}'


def native_path(prepared):
    return prepared / f'native.{configuration()["suffix"]}'


def validate_cpu(cpu):
    if configuration()["name"] == "arm-macos":
        if cpu is not None:
            raise ValueError("macOS does not support this runner's CPU affinity; omit --cpu")
    elif cpu is None or cpu not in os.sched_getaffinity(0):
        raise ValueError("Linux timing requires --cpu in the process's allowed affinity set")


def configure(cpu, native):
    validate_cpu(cpu)
    if configuration()["name"] == "x86-linux":
        os.sched_setaffinity(0, {cpu})
    else:
        native.bench_set_qos.argtypes = []
        native.bench_set_qos.restype = ct.c_int
        if native.bench_set_qos() != 0:
            raise RuntimeError("Cannot establish USER_INITIATED QoS")


def command(argv):
    result = subprocess.run(argv, capture_output=True, text=True, timeout=15)
    return dict(command=argv, returncode=result.returncode,
                stdout=result.stdout, stderr=result.stderr)


def snapshot(cpu):
    def read(path):
        try:
            return Path(path).read_text().strip()
        except OSError:
            return None
    result = dict(platform=configuration(), cpu=cpu, load=os.getloadavg())
    if configuration()["name"] == "arm-macos":
        result.update(affinity="unavailable on macOS", qos="QOS_CLASS_USER_INITIATED when timing",
                      hardware=command(["sysctl", "hw.model", "machdep.cpu.brand_string", "hw.ncpu",
                                        "hw.perflevel0.physicalcpu", "hw.perflevel1.physicalcpu"]),
                      os=command(["sw_vers"]), power=command(["pmset", "-g", "custom"]),
                      battery=command(["pmset", "-g", "batt"]), thermal=command(["pmset", "-g", "therm"]),
                      processes=command(["ps", "-axo", "pid,ppid,%cpu,comm", "-r"]),
                      frequency="not sampled; no privileged powermetrics during timings",
                      core_residency="unavailable; QoS does not pin a performance core")
    else:
        result.update(affinity=sorted(os.sched_getaffinity(0)),
                      cpuinfo=read("/proc/cpuinfo"),
                      governor=read(f"/sys/devices/system/cpu/cpu{cpu}/cpufreq/scaling_governor"),
                      frequency_khz=read(f"/sys/devices/system/cpu/cpu{cpu}/cpufreq/scaling_cur_freq"),
                      siblings=read(f"/sys/devices/system/cpu/cpu{cpu}/topology/thread_siblings_list"),
                      cpu_stat=read("/proc/stat"),
                      thermal={str(p): read(p) for p in Path("/sys/class/thermal").glob("thermal_zone*/temp")})
    return result


def linkage(native):
    """Record native dependency identity without reading implementation source."""
    if configuration()["name"] == "arm-macos":
        result = command(["otool", "-L", str(native)])
        if result["returncode"]:
            raise RuntimeError(result)
        return result["stdout"], [], dict(os=command(["sw_vers"]),
            identity="Apple system libm in the OS dyld shared cache; OS build and load commands recorded, not a standalone libm-file hash")
    result = command(["ldd", str(native)])
    if result["returncode"]:
        raise RuntimeError(result)
    files = []
    for line in result["stdout"].splitlines():
        if "=>" in line:
            path = Path(line.split("=>", 1)[1].strip().split()[0])
            if path.is_file():
                files.append(path.resolve())
    return result["stdout"], files, dict(libc=platform.libc_ver())
