#!/usr/bin/env bash

#set -x

target=$1
out_file=$2
threads=$3
branchname=$4

# Windows only: Visual Studio's command line to set up environment (VS_ENV_CMD)
if [[ $OS == "Windows_NT" ]] ; then
  # Starting from Visual Studio 2017, version 15.2 or later,
  # we can determine the location of a VS install
  # using vswhere.exe, see:
  # https://docs.microsoft.com/en-us/visualstudio/extensibility/locating-visual-studio
  if
    VSWHERE_WINDOWS="$(cmd.exe /C 'echo %ProgramFiles(x86)%\Microsoft Visual Studio\Installer\vswhere.exe' | sed 's!\r!!g')" &&
    VSWHERE=$(cygpath -u "$VSWHERE_WINDOWS") &&
    VS_HOME=$("$VSWHERE" -requires Microsoft.VisualStudio.Component.FSharp -format value -property InstallationPath | sed 's!\r!!g') &&
    [[ -n "$VS_HOME" ]]
  then
    # Visual Studio 2017 (15.2) or later
    # vcvarsall.bat has been superseded by vsdevcmd.bat, see:
    # https://docs.microsoft.com/en-us/dotnet/csharp/language-reference/compiler-options/how-to-set-environment-variables-for-the-visual-studio-command-line
    VSDEVCMD_PATH=$(cygpath -u "$VS_HOME")/Common7/Tools
    VSDEVCMD=$(cygpath -w "$VSDEVCMD_PATH/VsDevCmd.bat")
    # Here we assume that BOTH the target platform
    # and the host platform are amd64.
    VS_ENV_CMD='"'"$VSDEVCMD"'" -arch=amd64 -host_arch=amd64'
  else
    # Older versions are based on vcvarsall.bat
    if [[ -v VS140COMNTOOLS ]]; then
      # Visual Studio 2015 (14.x)
      VS_TOOLS_PATH="$VS140COMNTOOLS"
    elif [[ -v VS120COMNTOOLS ]]; then
      # Visual Studio 2012 (12.x)
      VS_TOOLS_PATH="$VS120COMNTOOLS"
    elif [[ -v VS110COMNTOOLS ]]; then
      # Visual Studio 2010 (10.x)
      VS_TOOLS_PATH="$VS110COMNTOOLS"
    else
      # Not found
      echo Could not find Visual Studio
      exit 1
    fi
    VCVARSALL_PATH="$VS_TOOLS_PATH"/../../VC
    VCVARSALL=$(cygpath -d "$VCVARSALL_PATH/vcvarsall.bat")
    # Here we assume that BOTH the target platform
    # and the host platform are amd64.
    VS_ENV_CMD="$VCVARSALL amd64"
  fi
fi

function export_home() {
    local home_path=""
    if command -v cygpath >/dev/null 2>&1; then
        home_path=$(cygpath -m "$2")
    else
        home_path="$2"
    fi

    export $1_HOME=$home_path

    # Update .bashrc file
    local s_token=$1_HOME=
    if grep -q "$s_token" ~/.bashrc; then
        sed -i -E "s@$s_token.*@$s_token$home_path@" ~/.bashrc
    else
        echo "export $1_HOME=$home_path" >> ~/.bashrc
    fi
}

function fetch_qd() {
    if [ ! -d qd ]; then
        git clone https://github.com/project-everest/quackyducky qd
    fi

    cd qd
    git fetch origin
    local ref=$(jq -c -r '.RepoVersions["qd_version"]' "$rootPath/.docker/build/config.json" )
    if [[ $ref == "" || $ref == "null" ]]; then
        echo "Unable to find RepoVersions.qd_version on $rootPath/.docker/build/config.json"
        return -1
    fi

    echo Switching to QuackyDucky $ref
    git reset --hard $ref
    cd ..
    export_home QD "$(pwd)/qd"
}

function fetch_and_make_qd() {
    fetch_qd

    # Default build target is all (quackyducky lowparse), unless specified otherwise
    local target
    if [[ $1 == "" ]]; then
        target="all"
    else
        target="$1"
    fi

    OTHERFLAGS='--admit_smt_queries true' make -C qd -j $threads $target
}

function build_pki_if() {
    if [[ -d src/pki ]]; then
        make -C src/pki -j $threads
    fi
}

function mitls_verify() {
    export_home MITLS "$(pwd)"

    # Figure out the branch
    CI_BRANCH=${branchname##refs/heads/}
    echo "Current branch_name=$CI_BRANCH"

    fetch_and_make_qd &&
    build_pki_if &&
    make -j $threads test -k
}

function mitls_verify_and_hints() {
    mitls_verify && refresh_mitls_hints
}

function refresh_mitls_hints() {
    # We should not generate hints when building on Windows
    if [[ "$OS" != "Windows_NT" ]]; then
        refresh_hints "git@github.com:mitls/mitls-fstar.git" "true" "regenerate hints" "src"
    fi
}

# Note: this performs an _approximate_ refresh of the hints, in the sense that
# since the hint refreshing job takes about 80 minutes, it's very likely someone
# merged to $CI_BRANCH in the meanwhile, which would invalidate some hints. So, we
# reset to origin/$CI_BRANCH, take in our hints, and push. This is short enough that
# the chances of someone merging in-between fetch and push are low.
function refresh_hints() {
    local remote=$1
    local extra="$2"
    local msg="$3"
    local hints_dir="$4"

    # Figure out the branch
    CI_BRANCH=${branchname##refs/heads/}
    echo "Current branch_name=$CI_BRANCH"

    # Add all the hints, even those not under version control
    find $hints_dir -iname '*.hints' -and -not -path '*/.*' -and -not -path '*/dependencies/*' | xargs git add

    # Without the eval, this was doing weird stuff such as,
    # when $2 = "git ls-files src/ocaml-output/ | xargs git add",
    # outputting the list of files to stdout
    eval "$extra"

    git commit --allow-empty -m "[CI] $msg"

    # Memorize that commit
    commit=$(git rev-parse HEAD)

    # Drop any other files that were modified as part of the build (e.g.
    # parse.fsi)
    git reset --hard HEAD

    # Move to whatever is the most recent master (that most likely changed in the
    # meantime)
    git fetch
    git checkout $CI_BRANCH
    git reset --hard origin/$CI_BRANCH

    # Silent, always-successful merge
    export GIT_MERGE_AUTOEDIT=no
    git merge $commit -Xtheirs

    # Push.
    git push $remote $CI_BRANCH
}

function exec_build() {

    result_file="../result.txt"
    local status_file="../status.txt"
    echo -n false >$status_file

    if [ ! -f miTLS_icla.txt ]; then
        echo "I don't seem to be in the right directory, bailing"
        echo Failure >$result_file
        return
    fi

    if [[ $target == "mitls_verify" ]]; then
        echo "target -> mitls_verify"
        mitls_verify && echo -n true >$status_file
    elif [[ $target == "mitls_verify_and_hints" ]]; then
        echo "target -> mitls_verify_and_hints"
        export OTHERFLAGS="--record_hints $OTHERFLAGS"
        mitls_verify_and_hints && echo -n true >$status_file
    else
        echo "Invalid target"
        echo Failure >$result_file
        return
    fi

    if [[ $(cat $status_file) != "true" ]]; then
        echo "Build failed"
        echo Failure >$result_file
    else
        echo "Build succeeded"
        echo Success >$result_file
    fi
}

# Some environment variables we want
export OCAMLRUNPARAM=b
export OTHERFLAGS="--use_hints --query_stats"
export MAKEFLAGS="$MAKEFLAGS -Otarget"

export_home FSTAR "$(pwd)/FStar"
export_home KREMLIN "$(pwd)/kremlin"
export_home HACL "$(pwd)/hacl-star"
export_home MLCRYPTO "$HACL_HOME/mlcrypto"
export_home OPENSSL "$MLCRYPTO_HOME/openssl"
export_home VALE "$HACL_HOME/valebin"
cd mitls-fstar
rootPath=$(pwd)
exec_build
cd ..
