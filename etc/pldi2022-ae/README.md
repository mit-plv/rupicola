# Relational Compilation for Performance-Critical Applications

Thanks for reviewing this artifact!  This README is intended to walk you through
our paper, code, and experiments.  We're excited to share Rupicola with you!

We have packaged the artifact as a virtual machine running Ubuntu.  You will
find CoqIDE and Emacs pre-installed in the VM, and we made sure to leave some
of free space on the hard drive should you want to install additional programs.

Please do let us know if your run into any issue: we intend for this artifact to
remain public after the review, and we're eager to fix any issue that may have
remained despite our testing.  Thanks!

## Getting started guide

> VM software
>   VirtualBox 6.1
> VM username
>   ae
> VM password and root password
>   ae
> Required expertise
>   Familiarity with the Coq proof assistant and its scripting language (Ltac).
>   Some experience reading C code.

- Please boot the VM, open a terminal, and navigate to `~/rupicola`.  From this
  directory you should be able to type `make -j` to compile the whole repository
  (it takes a few minutes when starting fresh, but everything is precompiled in
  the VM — if you want to rebuild everything, see “Rebuilding” below).

- In CoqIDE or Emacs, open `~/tutorial.v`.  This is an executable version of
  section 2 of the paper — the outputs in the paper were generated from an
  abbreviated version of this file.  Make sure that the full file compiles and
  runs.

- In CoqIDE or Emacs, open `~/rupicola/src/Rupicola/Examples/Uppercase.v`.  This
  is the code accompanying section 3 of the paper.  Make sure that the full file
  compiles and runs.

- In a terminal, navigate to `~/rupicola/src/Rupicola/Examples/` and run
  `./benchmark.sh`, followed by `./plot.py`, which should generate
  `benchmarks.pdf`

That's it!

Note: If you want to replicate this VM, it's very easy: it was created by
cloning the `pldi2022-ae` branch of our repository and running
`etc/pldi2022-ae/setup.sh`.  The repository itself can be found at
<https://github.com/mit-plv/rupicola.git> .

## Step-by-step guide

Here is a brief summary of the measurable claims that the paper makes, along
with details of how this artifact supports these claims:

- Table 1 and 2: Lines of lemma and proofs are measured directly from the source
  code; we give pointers to the relevant source below.

- Figure 2: We have precompiled all code and experiments, so reproducing the
  benchmarks is a matter of calling one single script and comparing the
  resulting PDF plots to the paper.

In addition, here are the criteria for the functional and reusable badges, along
with a description of how this artifact supports them:

**Consistency with the paper**
  We provide scripts to reproduce figures and data to reproduce the tables.

  → See “Section 4: Evaluation” below

**Completeness, the artifact should reproduce all the results that the paper reports**
  This artifact covers everything in the paper (plus some additional experiments!)

**Documentation**
  This README is constructed to be self-sufficient, but we include an executable
  version of Section 2's tutorial as a literate Coq file, as well as
  supplementary materials, pointers to an extended tutorial, over 100 pages of
  additional documentation, and a video presenting Rupicola and the motivation
  behind it.

  → See “Section 2: A relational compilation tutorial” and “Section 3:
  Getting started with Rupicola” below

**Ease of reuse: everything needed to build on top of the original work, including
source files together with a working build process that can recreate the
binaries provided**
  The whole system is free software under a permissive license; the build is
  automated, and we even provide the script that was used to build the VM, to
  automate the whole set up.

Additionally, we meet all three criteria (even though the instructions say
"or"?) for Reusable:

Artifacts with source can be considered Reusable:

**If they can be reused as components,**
  Our repo is structured as a library separated from a collection of examples.
  Each individual example is a self-contained demonstration of reusability of
  the core library.

  → See examples in the `~/rupicola/src/Examples/` folder

**If others can learn from the source and apply the knowledge elsewhere (e.g.,
learning an implementation or proof/formalization technique for use in a
separate codebase)**, or
  Our artifact includes a complete tutorial on relational compilation, which can
  even be consumed independently of the paper.  It is our hope that the artifact
  and paper will both help authors leverage relational compilation in their own
  projects.

  → See section 2 and 3 below.

**If others can directly modify and/or extend the system to handle new or expanded
use cases.**
  We provide instructions and suggestions of starting points to add your own
  extensions to Rupicola and build your own programs with Rupicola.

  → See “Running your own experiments” below

**Beyond this, we've done our best to abide by the criteria laid out in
SIGPLAN's experimental evaluation guidelines.**
(https://sigplan.org/Resources/EmpiricalEvaluation/)

Three caveats:

- Reproducing performance in a VM can be difficult.  If you are on a laptop, we
  recommend turning of frequency scaling, plugging in your charger, and
  minimizing activity outside the VM.  In general, desktop CPUs tend to have more
  stable performance.  That said, our experiments are designed to be relatively
  robust (in particular, we use cycle counts instead of wall clock time).

- It looks like error bars are missing in Figure 2 in the paper, but they are
  not missing — they're just very small.  In a VM we expect slightly larger
  fluctuations, and our plotting scripts will automatically compute adequate
  confidence intervals.

- We have made one change in Figure 2 compared to the submission.  Figure 2
  shows the performance of handwritten C code versus that of C code generated by
  Rupicola.  In one case, Rupicola generates faster code than our handwritten
  reference.

  Defining "handwritten code" can be tricky: since Rupicola generates C code,
  arguably anything that Rupicola does is fair game to do in handwritten code as
  well.  Thus, we have adjusted the C code for example `ip` to be smarter.  This
  allows the C compiler to generate code for our handwritten reference that is
  as fast as Rupicola's output.

  This change avoids long debates about what constitutes “handwritten” code.
  The claim in the paper's abstract that Rupicola can “generate low-level code
  with performance *on par* with that of handwritten C programs” is not
  affected.

---

Happy hacking!  If you are reading this tutorial in Emacs, you can use the
command `M-x ffap` (`find-file-at-point`) to open any of the file paths
mentioned below.

### On relational compilation: interactive tutorials

We start with two interactive walkthroughs.  If you just want to reproduce the
plots, skip to `Section 4: Evaluation` below.

### Section 2: A relational compilation tutorial

For this part, please open `~/tutorial.v` in CoqIDE or Emacs and follow the
tutorial.  This is an implementation of section 2 of the paper.  By the end, you
should be an expert on relational compilation!  We have written the tutorial to
be standalone, so it should not be necessary to read the whole paper to
understand it.

### Section 3: Getting started with Rupicola

For this part, please read the paper's section 3 side by side with the code in
`~/rupicola/src/Rupicola/Examples/Uppercase.v`.  The code is an implementation
of the example in the paper, which we included in hopes of making the paper
easier to follow.

Experimenting with this file is a good way to get a feel for Rupicola: you can
try changing parts of the source code and looking at what part of the derivation
breaks, for example.

By the way: “Rupicola Rupicola” is the scientific name of the Guianan
cock-of-the-rock — a fitting name, since Rupicola compiles from Coq to Bedrock!

### Additional documentation before diving into the evaluation

The following four resources provide a much more in-depth discussion of Rupicola;
they are of course completely optional reading.

- `~/supplementary.pdf`
  Supplementary examples and materials.

- https://youtu.be/BG3RXB8hZo4
  A talk on Rupicola.

- https://people.csail.mit.edu/cpitcla/thesis/relational-compilation.html
  A much longer version of the tutorial in section 2, which we have also
  included in PDF form as supplementary material in our submission.  We intend
  to deduplicate it with Section 2 and publish it online at a later point.

- http://adam.chlipala.net/theses/cpitcla.pdf
  A PhD thesis detailing relational compilation and its use for
  functional-to-imperative code generation for performance-critical
  applications.  It is essentially an expanded version of our PLDI paper, and it
  includes a detailed discussion of the benchmark, of vectorization issues,
  etc.

- `~/rupicola/etc/notes/faq.org`
  A (rough) FAQ that provides details on some design questions in Rupicola.

### Checking the proofs

The following command can be run to check our proofs:

    cd ~/rupicola/
    make -f Makefile

### Section 4: Evaluation

#### Table 1

The examples are taken from the following sources.  It should be straightforward
to step through all of them, if you are curious to see the code in action.  We
measure proof lines between `Proof.` and `Qed.` and we count “lemma” lines from
`Lemma` to `Proof.`

`nondet`
  `~/rupicola/src/Rupicola/Examples/Nondeterminism/StackAlloc.v`
    - `compile_stack_alloc`: 26 lines to state the lemma, 17 lines to prove it
  `~/rupicola/src/Rupicola/Examples/Nondeterminism/Peek.v`
    - `compile_peek`: 24 lines to state the lemma, 11 lines to prove it

  Hence the table line `26 + 24`, `17 + 11`.  The included times are a rough
  estimate of how long the first author needed to develop the proofs.

`cells`
  `~/rupicola/src/Rupicola/Examples/Cells/Cells.v`:
    - `compile_get`: 22 + 5 lines
    - `compile_put`: 23 + 3 lines
  `~/rupicola/src/Rupicola/Examples/Cells/IndirectAdd.v`:
    - `compile_indirect_add`: 31 lines to state the lemma, 7 lines to prove it

`io`
  `~/rupicola/src/Rupicola/Examples/IO/Echo.v`:
    - `compile_readw`: 25 + 7 lines
    - `compile_writew`: 26 + 10 lines

### Table 2

The counting methodology is the same as for table 1 and taken from the following
sources:

`crc32`: `~/rupicola/src/Rupicola/Examples/CRC32/CRC32.v`
  Error-detecting code (cyclic redundancy check)
`utf8`: `~/rupicola/src/Rupicola/Examples/Utf8/Utf8.v`
  Branchless UTF-8 decoding
`m3s`: `~/rupicola/src/Rupicola/Examples/Arithmetic.v` (module `Murmur3`)
  Scramble part of the Murmur3 algorithm
`upstr`: `~/rupicola/src/Rupicola/Examples/Uppercase.v`
  In-place string uppercase (\autoref{box:uppercase})
`ip`: `~/rupicola/src/Rupicola/Examples/Net/IPChecksum/IPChecksum.v`
  IP (one's-complement) checksum (RFC 1071)
`fasta`: `~/rupicola/src/Rupicola/Examples/RevComp.v`
  In-place DNA sequence complement
`fnv1a`: `~/rupicola/src/Rupicola/Examples/Arithmetic.v` (module `FNV1A`)
  Fowler-Noll-Vo (noncryptographic) hash
`l64x128`: `~/rupicola/src/Rupicola/Examples/L64X128.v`
  A modern pseudorandom number generator

### Figure 2

To reproduce Figure 2 (you may have already followed the steps below as part of
the kick-the-tires phase):

- In a terminal, navigate to `~/rupicola/src/Rupicola/Examples/`
- Run `./benchmark.sh` to collect data, which will take a few minutes
- Run `./plot.py` to generate `benchmarks.pdf`
- Compare `plot.pdf` to the figure in the paper (the colors will be different,
  since the plotting script needs to accommodate as many compilers as are
  available on the machine)

Beyond the caveat in the intro (we have improved the handwritten implementation
of ip, and it now matches the performance of the code generated by Rupicola), it
is unlikely that you will observe the *exact* same ratios between compilers and
benchmarks.  The reason is that different computer chips support different
instructions and hence different optimizations.  For example, Clang 13 is a bit
slower than GCC on `fasta` on an i7-5930K, but on par with GCC on an i5-1135G7.
This sort of variability is why our plots include multiple compilers and a
variety of examples.

---

That's it!  You have reproduced every result in the paper, and hopefully learned
something interesting in the process!

If you're curious, here is how the plots work.  Each benchmark includes a script
`ubench.sh`, as well as a manual C implementation of the same algorithm, and a
driver for the C code generated by Rupicola.  Both pieces of C code are
benchmarked in the same conditions.  We use a CPU instruction (`rdtsc`) to
measure clock cycles, which is much more robust that wall clock time.

Concretely, for e.g. `Uppercase.v`, we have in
`~/rupicola/src/Rupicola/Examples/`:

`Uppercase.v`
  The Coq source code.  Note the fragment at the end that generates C code:
  ```coq
  Definition upstr_cbytes := Eval vm_compute in
    list_byte_of_string (ToCString.c_module [upstr_br2fn]).
  ```
`Uppercase/testdata.c`
  A generator that produces `testdata.bin`, the data fed to the C programs
`Uppercase/upstr_c.c`
  The handwritten C version of the algorithm
`Uppercase/ubench.c`
  A C driver for the benchmarks
`Uppercase/ubench.sh`
  A script that prints out `upstr_bytes` from the Coq file into
  `upstr_rupicola.c`, then runs the benchmarks
`Uppercase/upstr_rupicola.c` (auto-generated)
  The Rupicola-generated C version of the algorithm

Note that we invoke `ubench.c` once per benchmark: if we ran both benchmarks in
the same process we would risk running one of the programs with a cold cache and
the other one with a hot cache.

## Going further: creating your own examples and running extra experiments

This entire section is optional.

### Creating your own examples

To get you started, we wrote up a small exercise for the artifact evaluation,
found in `rupicola/src/Examples/Exercises/ByteOps.v`.  It explores an extension
of Rupicola's expression compiler by using an arithmetic operator that is not
supported out of the box by Rupicola and looking at how the compiler breaks and
how support can be added for the new operator.  A solution (in the form of a
literate program) is in `~/rupicola/src/Examples/Exercises/ByteOps_Solution.v`.

Here some other tasks that you may consider:

- Compile a new small program, for example one that computes the max of three
  numbers (for an additional twist, read the three numbers from an array).  The
  files `Examples/Conditionals.v` and `Examples/Arrays.v` are good places to
  start from.

- Change the `Uppercase` example to apply a different transformation on strings.
  For example, write a string sanitizer that replaces every non-printable
  character by a space.  If you get stuck, look at `RevComp.v` for inspiration.

Other good files to draw inspiration from are `Expr.v`, `Arith.v`, and `Utf8.v`.
After that, your imagination is the limit!  Don't hesitate to ask if you run
into issues.

### Running additional benchmarks

#### OCaml benchmarks

The paper does not provide a detailed benchmark between Coq-generated OCaml and
Rupicola-generated C code; instead it simply claims “suffice to say that a
typical result there is a speedup of about 200× when extracting with Rupicola.”

- In a terminal, navigate to `~/rupicola/src/Rupicola/Examples/`
- Run `./ocaml_benchmark.sh` to collect data (about a minute)
- Re-run `./plot.py` to generate `benchmark-ocaml.pdf`

The benchmark uses Jane Street's `Ocaml_intrinsics` library to measure CPU
cycles precisely.

The resulting plot compares the performance of Rupicola-generated C and
Coq-generated OCaml.  The OCaml code is the result of adding manual, unsafe
extraction directives in Coq to make the code faster.  Without that, the code
runs for hours.

In fact, if you are *really* curious, you can open
`~/rupicola/src/Rupicola/Examples/Net/IPChecksum/ubench_ocaml.ml` and uncomment
the three commented-out benchmarks… but be ready to spend hours or days watching
a blank terminal (we lost patience up after 2 hours, given that the C code takes
milliseconds; the code spends forever copying data around and doing quadratic
traversals of everything, so to get anything reasonable you'll want to change
the input size in `testdata.c`).

#### Benchmarking with additional compilers

The compilation scripts are setup to pick up all compilers that they can find
from GCC 9 to GCC 9 to 11 and Clang 11 to 13.  The plotting scripts are the
same.  To keep the VM size reasonable we only included those shown in the
paper's plot, but if you want to run more experiments you can simply `apt
install gcc-10 gcc-11 clang-11 clang-12` and rerun `benchmark.sh` and `plot.py`

## Running on your own machine

The repository is at <https://github.com/mit-plv/rupicola/>, and a complete
setup and build process is provided as a commented script in
`~/rupicola/etc/pldi2022-ae/setup.sh`.  We recommend reading through that file
if you prefer to run everything on your own machine.

You can clone the repository that this VM was built from using

    git clone --recursive https://github.com/mit-plv/rupicola.git -b pldi2022-ae

In fact, the whole VM was built just by running the script found at
`etc/pldi2022-ae/setup.sh` in the repository.

We develop and test Rupicola only on GNU/Linux machines, though we have had
students use it on macOS machines as well.

### Building from scratch

Use `make cleanall` to remove all build artifacts.  Use `make -j` to rebuild
everything.  The build can be pretty chatty at times, and some of the libraries
we depend on (including Bedrock2 and coqutils) have build-time warnings (mostly
due to backwards compatibility concerns).

# Conclusion

That's all!  Thanks so much for volunteering to join the AEC.
