miTLS: A verified reference implementation of TLS
=================================================

This repository contains the new F* development a port of the stable [F# development](https://github.com/mitls/mitls-flex) to F* 0.9.

[![Build status](https://travis-ci.org/mitls/mitls-fstar.svg?branch=master)](https://travis-ci.org/mitls/mitls-fstar)

### miTLS website

More information on miTLS can be found at www.mitls.org

More information on F\* can be found at www.fstar-lang.org

### Table of contents

  * [Building](#building)
  * [Directory structure](#directory-structure)
  	* [Legacy, imported from mitls-f7](#legacy-imported-from-mitls-f7)
  * [Configuring Emacs and Atom F* modes](#configuring-emacs-and-atom-f-modes)

### Building

There are two ways to setup your build environment. 
  * [Using Docker](#docker)
  * [Custom setup using Cygwin and OCaml](#cygwin)

#### Using Docker 
Head over to https://github.com/mitls/mitls-fstar/wiki/Setting-up-a-Docker-based-Development-environment for instructions on setup

#### Custom setup using Cygwin and OCaml
There are numerous dependencies. Follow the instructions at https://github.com/protz/ocaml-installer/wiki to have a working Cygwin and OCaml setup. In addition to `ocamlfind`, `batteries`, `stdint`, and `zarith`, you will also need to install the `sqlite3` package (hint: `opam install sqlite3`). To build CoreCrypto, you will need to install `libssl-dev`. On Windows, you can use `opam depext ssl` to install the appropriate Cygwin packages.

Once this is done, head over to https://github.com/mitls/mitls-fstar/wiki/Development-environment for some tips on our development environment, including how to attain happiness with Cygwin & Git on Windows (hopefully).

After the setup is done, check that you have the F\* compiler set up and running in `.fstar` (`git submodule update --init` if you need to). Note: we do not support the F\# build of F\*; please use the OCaml build of F\* (i.e. `make -C .fstar/src/ocaml-output`).

To verify the current miTLS:
```
cd src/tls
make all-ver -j N
```
where N is the number of parallel jobs to use.

To build the mitls.exe command line tool:
```
cd src/tls
make mitls.exe
./mitls.exe -v 1.2 google.com
./mitls.exe -s 0.0.0.0 4443 &
./mitls.exe 127.0.0.1 4443
```

**Caveats:**

There is a script that detects if the `fstar` module has changed since the last build, and rebuilds it. If you get strange errors, the script may have failed to reubild `fstar` properly, and the main `Makefile` keeps attempting to extract/verify using an outdated version of F\*. In that case, it's a good idea to run `make -C .fstar/src/ocaml-output clean all`.

### Directory structure

- `src/`

 - `tls/` In-progress miTLS port. Most files have been ported and fully typecheck; others only lax typecheck or still need to be ported. The `Makefile` here has two targets that are also part of regression testing:

    - `tls-ver` Full type checking of files that have been ported so far (listed in variable `VERIFY`)
    - `tls-gen`  OCaml code generation for files ported so far---generated files go to the `output/` directory
    - `mitls.exe` openssl-like command line client and server. See `mitls.exe --help` for details on how to use the tool.

  - `fstar_proof/` an independent POPL'16 example, verifying the state machine in F* (out of date, JK is the expert; it could be moved to FStarLang/FStar).

  - `mipki/` Antoine's development on certificate management.

  - `flex/` WIP port of flexTLS to F*

#### Legacy, imported from mitls-f7

- `apps/` Sample apps built on top of miTLS --- not ported yet.

- `data/` Persistent data used by miTLS, e.g. the OpenSSL root certificate store; sample chains for the test server; a DH parameter cache --- not ported yet.

- `libs/` miTLS libraries; CoreCrypto and Platform had been moved to `FStarLang/FStar/contrib` and remaining files are deprecated, DHDB remains to be ported.
  - `fst` F* specification
  - `fs` F# implementation
  - `ml` OCaml implementation

- `scripts/` Legacy scripts for distribution-management.

- `tests/` Legacy test suit

- `VS/` miTLS Visual Studio solution, for browsing/building the old F# files in `src/tls-fs` --- used to build as reference; currently broken.


### Configuring Emacs mode

The Makefile in `src/tls` has the following targets:

- `make <file.fst(i)>-ver` verifies an individual file.
- `make <file.fst(i)>-in` generates command-line arguments to use with the `--in` flag to verify `<file.fst(i)>`.
This target can be used to pass appropriate arguments in `fstar-mode.el` using this snippet:

```elisp
(defun my-fstar-compute-prover-args-using-make ()
  "Construct arguments to pass to F* by calling make."
  (with-demoted-errors "Error when constructing arg string: %S"
    (let* ((fname (file-name-nondirectory buffer-file-name))
	   (target (concat fname "-in"))
	   (argstr (car (process-lines "make" "--quiet" target))))
      (split-string argstr))))

(setq fstar-subp-prover-args #'my-fstar-compute-prover-args-using-make)
```

If you use F* for other projects that lack a Makefile with a <file.fst(i)-in> target, you may want to use some default list of command-line arguments if `make <file.fst(i)-in>` fails, using, e.g.

```elisp
(defun my-fstar-compute-prover-args-using-make ()
  "Construct arguments to pass to F* by calling make."
  (with-demoted-errors "Error when constructing arg string: %S"
    (let* ((fname (file-name-nondirectory buffer-file-name))
	   (target (concat fname "-in"))
	   (argstr (condition-case nil
		       (car (process-lines "make" "--quiet" target))
		     (error "--debug Low"))))
      (split-string argstr))))
```

Error messages shown in the mini-buffer are sometimes truncated. It can be convenient to set the debug flag and open the `*Messages*` buffer in another window to see exactly what is going on. To make Emacs follow the end of the `*Messages*` buffer, use this snippet:

```elisp
(setq fstar-subp-debug t)

(defadvice message (after message-tail activate)
  "goto point max after a message"
  (with-current-buffer "*Messages*"
    (goto-char (point-max))
    (walk-windows
     (lambda (window)
       (if (string-equal (buffer-name (window-buffer window)) "*Messages*")
           (set-window-point window (point-max))))
     nil
     t)))
```
