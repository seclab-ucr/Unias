# Unias
A Hybrid Alias Analysis that unifies dataflow-based and type-based methods

To start with, first specif your environment (recommand Release build) of LLVM (recommand 14.0.6) and SVF (recoomand https://github.com/SVF-tools/SVF/releases/tag/SVF-2.5) in CMakeLists.txt:

```
set(ENV{LLVM_DIR} /path/to/your/llvm/14.0.6/build/lib/cmake)
set(ENV{SVF_DIR} /path/to/your/SVF/root/SVF-SVF-2.5) # There should be a Release-build/ or Debug-build/ folder in the SVF-SVF-2.5/
```

Currently only works on -O0 optimization, e.g., no special handling for multiindices getElementPtr instructions. Will release the way to modify, compile and link -O0 whole kernel soon.

To build

```
mkdir build
cd build
cmake .. -DCMAKE_BUILD_TYPE=Release
make -j 8
```

Sample command to query aliases of modprobe_path

```
build/bin/UniasAnalysis ./input/vmlinux.bc -SpecificGV=modprobe_path
```

Updates about GEP edge byteoffset are fixing and comming soon...

Ref

https://www.usenix.org/conference/usenixsecurity23/presentation/li-guoren

```
@inproceedings{lihybrid,
  title={A Hybrid Alias Analysis and Its Application to Global Variable Protection in the Linux Kernel},
  author={Li, Guoren and Zhang, Hang and Zhou, Jinmeng and Shen, Wenbo and Sui, Yulei and Qian, Zhiyun},
  booktitle={32st USENIX Security Symposium (USENIX Security 23)},
  pages={4211--4228},
  year={2023}
}
```