# Class Field Theory

An ongoing project to formalize the main theorems of local and global class field theory
in the Lean theorem prover.

This is the main repository for the 2025 Clay Maths summer school
[Formalizing Class Field Theory](https://www.claymath.org/events/formalizing-class-field-theory/).

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

## Using the project

There are two ways that you can interact with the project.

A *local installation* (recommended) involves installing Lean and the project locally on your
computer. Advantages: you can hack on the project without any internet access.
Disadvantages: if your computer is slow or if you don't have much memory, it might
be quite a painful process to use Lean this way.

Interacting *online* with the project involves connecting to a website where you can
see and change the code. Advantages: you get a reasonable experience even with a very
slow machine, and you don't have to find a couple of gigabytes of ram to store the project.
Disadvantages: you have to create an account on some website, you can only interact with
the project when you are online.

We explain both methods below.

## Local installation

First you need to install Visual Studio Code and the Lean 4 extension. Instructions for doing that are [here](https://docs.lean-lang.org/lean4/doc/quickstart.html).

Once you have VS Code and the Lean 4 extension, create a folder for your lean projects.
You could call it `my_lean_projects` (to be on the safe side, don't put any non-English
characters in this name and maybe don't put any spaces either). Now let's begin the process
of downloading and installing the class field theory project into this folder.

Fire up VS Code, open any file on your system in VS Code, and then click on the upside-down A

![an upside-down A](png/clone_forall.png?raw=true "an upside-down A")

and select `Open Project` -> `Download Project`. You don't want Mathlib or Mathematics In Lean,
you want the class field theory project. So type in the following Git repository URL into the text box which appeared:

```
https://github.com/kbuzzard/ClassFieldTheory
```

Now select your lean projects folder, and where it says "save as", type in the name of the
directory where you want to download the class field theory project (for example you could call
it `class_field_theory`) and click on "create project folder". Now wait for a couple of minutes
whilst everything downloads and compiles.

When it's all done, VS Code will ask if you want to open the project folder. Say yes
and you should be ready to go! Open up VS Code's file explorer (it looks like this)

![File explorer](png/file_explorer.png?raw=true "File explorer")

and navigate to the `ClassFieldTheory` directory, where you should find a whole bunch of directories containing the code.

### Local installation via command line

If you are an old hand, already have Lean installed, know what a command line is,
and just want to download the project from the command line, then it's

```bash
git clone https://github.com/kbuzzard/ClassFieldTheory.git
cd ClassFieldTheory
lake exe cache get
```

Now open the folder `ClassFieldTheory` which you just created, using VS Code's "open folder" functionality. You will find all the code inside a subdirectory also called `ClassFieldTheory`.

## Online play

If you don't have the 4.5 gigabytes necessary to install all this, or if your computer is too slow to make the experience of using Lean on it fun (you'll need at least 8 gigs of ram, for example), then you can work on the repository through a web browser (and you don't need to install anything onto your computer using this method).

### Method 1: via Gitpod.

Just click here: [![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/kbuzzard/ClassFieldTheory)

### Method 2: via Codespaces

Just click here: [![Open in Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/kbuzzard/ClassFieldTheory)
