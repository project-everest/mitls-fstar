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

SCONS_PYTHON_MAJOR=3
SCONS_PYTHON_MINOR=6
SCONS_PYTHON_MAJOR_MINOR=$SCONS_PYTHON_MAJOR.$SCONS_PYTHON_MINOR

run_scons () {
  short_dir="$1"
  shift
  cmd="$1"

  if [[ $OS == "Windows_NT" ]] ; then
    DIR=$(cygpath -w "$(pwd)"/"$short_dir")
  else
    DIR="$short_dir"
  fi

  if [[ $OS == "Windows_NT" ]]; then
    # Instead of invoking cmd.exe /c, which would force us to
    # rely on its flaky semantics for double quotes,
    # we go through a batch file.
    THIS_PID=$$
    # Find an unambiguous file name for our .bat file
    SCONS_EXECS=0
    while
      SCONS_INVOKE_FILE="everest$THIS_PID""scons$SCONS_EXECS"".bat" &&
      [[ -e "$SCONS_INVOKE_FILE" ]]
    do
      SCONS_EXECS=$(($SCONS_EXECS + 1))
    done
    # Then create, run and remove the .bat file
    cat > "$SCONS_INVOKE_FILE" <<EOF
call $VS_ENV_CMD
cd "$DIR"
EOF
    if command -v scons.bat > /dev/null 2>&1 ; then
      echo "call scons.bat $cmd $parallel_opt" >> "$SCONS_INVOKE_FILE"
    else
      PYDIR=$(cygpath -d $(windows_scons_python_dir))
      echo "$PYDIR/python.exe $PYDIR/Scripts/scons.py $cmd $parallel_opt" >> "$SCONS_INVOKE_FILE"
    fi
    chmod +x "$SCONS_INVOKE_FILE"
    "./$SCONS_INVOKE_FILE"
    SCONS_RETCODE=$?
    rm -f "$SCONS_INVOKE_FILE"
    return $SCONS_RETCODE
  else
    python$SCONS_PYTHON_MAJOR_MINOR $(which scons) -C "$DIR" $cmd $parallel_opt
  fi
}

run_vale_scons () {
  if [[ $OS == "Windows_NT" ]] ; then
    # Use the same Z3 for Dafny as for F*
    # i.e. the one in the PATH
    Z3PATH_UNIX=$(which z3.exe)
    Z3PATH=$(cygpath -w "$Z3PATH_UNIX")
    # Here the path to z3 might have whitespaces,
    # so it must be enclosed into double quotes
    # to be treated correctly by scons and Dafny.
    # Moreover, it must fit in the single argument to
    # run_vale_scons, which is why we cannot quote the command
    # as a member of the verify_commands array
    run_scons vale "--DARGS=/z3exe:\"$Z3PATH\" $1"
  else
    run_scons vale "$1"
  fi
}

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

# By default, HACL* master works against F* stable. Can also be overridden.
function fetch_hacl() {
    if [ ! -d hacl-star ]; then
        git clone https://github.com/mitls/hacl-star hacl-star
    fi

    cd hacl-star
    git fetch origin
    local ref=$(if [ -f ../.hacl_version ]; then cat ../.hacl_version | tr -d '\r\n'; else echo origin/master; fi)
    echo Switching to HACL $ref
    git reset --hard $ref
    git clean -fdx
    cd ..
    export_home HACL "$(pwd)/hacl-star"
    export_home EVERCRYPT "$(pwd)/hacl-star/providers"
}

# By default, kremlin master works against F* stable. Can also be overridden.
function fetch_kremlin() {
    if [ ! -d kremlin ]; then
        git clone https://github.com/FStarLang/kremlin kremlin
    fi

    cd kremlin
    git fetch origin
    local ref=$(if [ -f ../.kremlin_version ]; then cat ../.kremlin_version | tr -d '\r\n'; else echo origin/master; fi)
    echo Switching to KreMLin $ref
    git reset --hard $ref
    cd ..
    export_home KREMLIN "$(pwd)/kremlin"
}

function fetch_and_make_kremlin() {
    fetch_kremlin

    # Default build target is minimal, unless specified otherwise
    local target
    if [[ $1 == "" ]]; then
        target="minimal"
    else
        target="$1"
    fi

    make -C kremlin -j $threads $target ||
        (cd kremlin && git clean -fdx && make -j $threads $target)
    OTHERFLAGS='--admit_smt_queries true' make -C kremlin/kremlib -j $threads
    export PATH="$(pwd)/kremlin:$PATH"
}

function fetch_qd() {
    if [ ! -d qd ]; then
        git clone https://github.com/project-everest/quackyducky qd
    fi

    cd qd
    git fetch origin
    local ref=$(if [ -f ../.qd_version ]; then cat ../.qd_version | tr -d '\r\n'; else echo origin/master; fi)
    echo Switching to QuackyDucky $ref
    git reset --hard $ref
    cd ..
    export_home QD "$(pwd)/qd"
}

function fetch_and_make_qd() {
    fetch_qd

    # Default build target is quackyducky, unless specified otherwise
    local target
    if [[ $1 == "" ]]; then
        target="quackyducky"
    else
        target="$1"
    fi

    make -C qd -j $threads $target ||
        (cd qd && git clean -fdx && make -j $threads $target)
}

function build_pki_if() {
    if [[ -d src/pki ]]; then
        make -C src/pki -j $threads
    fi
}

function fetch_vale() {
    if [ ! -d vale ]; then
        git clone https://github.com/project-everest/vale vale
    fi

    cd vale
    git fetch origin
    local ref=$(if [ -f ../.vale_version ]; then cat ../.vale_version | tr -d '\r\n'; else echo origin/master; fi)
    echo Switching to Vale $ref
    git reset --hard $ref
    nuget restore tools/Vale/src/packages.config -PackagesDirectory tools/FsLexYacc
    cd ..
    export_home VALE "$(pwd)/vale"
}

function fetch_and_make_vale() {
    fetch_vale

    run_vale_scons "-j $threads --FSTAR-MY-VERSION"
}


function mitls_verify() {
    export_home MITLS "$(pwd)"

    # Figure out the branch
    CI_BRANCH=${branchname##refs/heads/}
    echo "Current branch_name=$CI_BRANCH"

    fetch_and_make_kremlin all &&
    fetch_and_make_qd &&
    # Build LowParse first, it is a dependency of miTLS anyway
    make -C src/lowparse -f Makefile.LowParse -j $threads -k &&
    { echo false > lowparse_examples_success ; } &&
    { echo false > mitls_success ; } && {
        # Perform LowParse CI and miTLS CI in parallel
        {
            if echo "$CI_BRANCH" | grep '^taramana_lowparse_ci_' ; then
                echo This is a LowParse CI-only branch. No miTLS CI here.
            else
                # miTLS CI proper starts here
                fetch_and_make_vale &&
                fetch_hacl &&
                    # Only building a subset of HACL* for now, no verification
                    OTHERFLAGS="--admit_smt_queries true $OTHERFLAGS" \
                    VALE_SCONS_PARALLEL_OPT="-j $threads --NO-VERIFY --FSTAR-MY-VERSION --VALE-MY-VERSION" \
                    make -C hacl-star providers.build -j $threads &&
                    make -C libs/ffi -j $threads &&
                    build_pki_if &&
                    make -C src/tls -j $threads all -k &&
                    make -C src/tls -j $threads test -k
            fi &&
            { echo true > mitls_success ; }
        } &
        {
            # Test LowParse examples
            make -C src/lowparse -f Makefile.LowParseExamples -j $threads -k &&
            { echo true > lowparse_examples_success ; }
        } &
        wait
    } &&
    $(cat lowparse_examples_success) &&
    $(cat mitls_success)
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
export OTHERFLAGS="--print_z3_statistics --use_hints --query_stats"
export MAKEFLAGS="$MAKEFLAGS -Otarget"

export_home FSTAR "$(pwd)/FStar"
cd mitls-fstar
exec_build
cd ..
