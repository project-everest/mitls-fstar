#!/bin/bash
# Starting from Visual Studio 2017, version 15.2 or later,
# we can determine the location of a VS install
# using vswhere.exe, see:
# https://docs.microsoft.com/en-us/visualstudio/extensibility/locating-visual-studio
# https://blogs.msdn.microsoft.com/vcblog/2017/03/06/finding-the-visual-c-compiler-tools-in-visual-studio-2017/
if
    VSWHERE_WINDOWS="$(cmd.exe /C 'echo %ProgramFiles(x86)%\Microsoft Visual Studio\Installer\vswhere.exe' | sed 's!\r!!g')" &&
    VSWHERE=$(cygpath -u "$VSWHERE_WINDOWS") &&
    VS_HOME=$("$VSWHERE" -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 -format value -property InstallationPath | sed 's!\r!!g') &&
    VC_VERSION=$(cat "$VS_HOME"/VC/Auxiliary/Build/Microsoft.VCToolsVersion.default.txt | sed 's!\r!!g' | sed 's![[:space:]]*$!!') &&
    [[ -n "$VS_HOME" ]]
then
  VS_BIN_DOSPATH="$VS_HOME"/VC/Tools/MSVC/"$VC_VERSION"/bin/Hostx64/x64
else
  # Older versions are based on vcvarsall.bat
  if [[ -v VS140COMNTOOLS ]]; then
      # Visual Studio 2015 (14.x)
      VS_BIN_DOSPATH="$VS140COMNTOOLS"/../../VC/bin
   elif [[ -v VS120COMNTOOLS ]]; then
      # Visual Studio 2012 (12.x)
      VS_BIN_DOSPATH="$VS120COMNTOOLS"/../../VC/bin
  elif [[ -v VS110COMNTOOLS ]]; then
      # Visual Studio 2010 (10.x)
      VS_BIN_DOSPATH="$VS110COMNTOOLS"/../../VC/bin
  else
    # Not found
    echo Could not find Visual Studio
    exit 1
  fi
fi

VS_BIN=$(cygpath -u "$VS_BIN_DOSPATH")

echo "$VS_BIN"
