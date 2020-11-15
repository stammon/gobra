<img src=".github/docs/gobra.png" height="250">

[![Test Status](https://github.com/viperproject/gobra/workflows/test/badge.svg?branch=master)](https://github.com/viperproject/gobra/actions?query=workflow%3Atest+branch%3Amaster)
[![License: MPL 2.0](https://img.shields.io/badge/License-MPL%202.0-brightgreen.svg)](./LICENSE)

[Gobra](https://www.pm.inf.ethz.ch/research/gobra.html) is a prototype verifier for Go programs, based on the [Viper verification infrastructure](https://www.pm.inf.ethz.ch/research/viper.html).

We call annotated Go programs Gobra programs and use the file extension `.gobra` for them. Examples can be found in [`src/test/resources`](https://github.com/viperproject/gobra/blob/master/src/test/resources).

## Compile and Run Gobra

### Preliminaries

- Java 64-Bit (tested with version 11)
- SBT (tested with version 1.2.6)
- Git

### Installation

1. Create a folder for your Gobra development. We will refer to this folder as `gobraHome`.
2. Clone Gobra and Viper dependencies
   - Change directory to `gobraHome`
   - [silver](https://github.com/viperproject/silver)
   - [silicon](https://github.com/viperproject/silicon)
   - [carbon](https://github.com/viperproject/carbon)
   - [viperserver](https://github.com/viperproject/viperserver)
   - Gobra
3. Add symbolic links
   - To create a symbolic link from A to B, you have to run
     - `mklink /D A B` (Windows (as admin)) resp.
     - `ln -s B A` (Linux & macOS) (use forward instead of backward slashes in the following)
   - Change directory to `gobraHome/silicon` and create the symbolic links:
     - silver -> ..\silver
   - Change directory to `gobraHome/carbon` and create the symbolic links:
     - silver -> ..\silver
   - Change directory to `gobraHome/viperserver` and create the links:
     - silver -> ..\silver
     - silicon -> ..\silicon
     - carbon -> ..\carbon
   - Change to `gobraHome/gobra-one` and create the links:
     - silver -> ..\silver
     - silicon -> ..\silicon
     - carbon -> ..\carbon
     - viperserver -> ..\viperserver
4. Install Z3 and Boogie.
   Steps (iii) and (iv) are specific to Boogie and only necessary when using Carbon as verification backend.
   1. Get a Z3 executable. A precompiled executable can be downloaded [here](https://github.com/Z3Prover/z3/releases).
      We tested version 4.8.6 64-Bit.
   2. Set the environment variable `Z3_EXE` to the path of your Z3 executable.
   3. Get a Boogie executable. Instructions for compilation are given [here](https://github.com/boogie-org/boogie).
      [Mono](https://www.mono-project.com/download/stable/) is required on Linux and macOS to run Boogie.
      Alternatively, extract a compiled version from the Viper release tools
      ([Windows](http://viper.ethz.ch/downloads/ViperToolsReleaseWin.zip), [Linux](http://viper.ethz.ch/downloads/ViperToolsReleaseLinux.zip), [macOS](http://viper.ethz.ch/downloads/ViperToolsReleaseMac.zip)).
   4. Set the environment variable `BOOGIE_EXE` to the path of your Boogie executable.

### Compilation

1. Change directory to `gobraHome/gobra-one`
2. Start an sbt shell by running `sbt`
3. Compile gobra-one by running `compile` in the sbt shell
   - **Important**: Do not compile silver, silicon, or carbon separately.
     If you have compiled them separately, then delete all target folders in these projects.
4. Check your installation by executing all tests (`test` in the sbt shell)
5. A file can be verified with `run -i path/to/file` in the sbt shell
   - e.g. `run -i src/test/resources/regressions/examples/swap.gobra`
6. All command line arguments can be shown by running `run --help` in the sbt shell

### Assembly

1. In an sbt shell, run `assembly`. The fat jar is then located in the target/scala folder.
2. To verify a file, run `java -jar -Xss128m gobra.jar -i path/to/file`

## Licensing

Most Gobra sources are licensed under the Mozilla Public License Version 2.0.
The [LICENSE](./LICENSE) lists the exceptions to this rule.
Note that source files (whenever possible) should list their license in a short header.
Continuous integration checks these file headers.
The same checks can be performed locally by running `npx github:viperproject/check-license-header#v1 check --config .github/license-check/config.json --strict` in this repository's root directory.

## Usage Instructions

```m
Usage: Gobra -i <input-files or a single package name> [OPTIONS]
Options:
     --backend  <arg>      Specifies the used Viper backend, one of SILICON,
                           CARBON (default: SILICON)
     --boogieExe  <arg>    The Boogie executable
 -d, --debug               Output additional debug information
     --nodebug
     --eraseGhost          Print the input program without ghost code
     --noeraseGhost
     --goify               Print the input program with the ghost code
                           commented out
     --nogoify
 -I, --include  <arg>...   Uses the provided directories to perform
                           package-related lookups before falling back to
                           $GOPATH
 -i, --input  <arg>...     List of Gobra programs or a single package name to
                           verify
     --logLevel  <arg>     One of the log levels ALL, TRACE, DEBUG, INFO, WARN,
                           ERROR, OFF (default: OFF)
     --parseOnly           Perform only the parsing step
     --noparseOnly
     --printInternal       Print the internal program representation
     --noprintInternal
     --printVpr            Print the encoded Viper program
     --noprintVpr
     --unparse             Print the parsed program
     --nounparse
     --z3Exe  <arg>        The Z3 executable
 -h, --help                Show help message
 -v, --version             Show version of this program
```
