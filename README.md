# Software Foundations: Coq & Lean 4

This repository contains porting the **Software Foundations** book (originally written in **Coq**) into **Lean 4**. It serves as a side-by-side learning resource for Formal Verification.

## Prerequisites & Installation

To run the code in this repository, you need the specific languages installed.

### 1. Lean 4 Setup
Lean 4 is much easier to set up than older provers. It handles its own dependencies via `elan`.

**Installation Steps:**
1.  **Install the Extension:** Install the [Lean 4](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) extension.
2.  **Install Elan (Version Manager):**
    * **Mac/Linux:**
        ```bash
        curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
        ```
    * **Windows:**
        ```powershell
        curl -O --location https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1
        powershell -ExecutionPolicy Bypass -f elan-init.ps1
        ```

**About `Lake`:**
Lake is the build system for Lean (like Cargo for Rust). While you can read files without it, you need it to manage the project structure. This project is initialized with Lake.

### 2. Coq (Rocq) Setup
If you want to run the original `.v` files to compare the syntax.

**Installation Steps:**
1.  **Install Coq:** The easiest way is via the [Coq Platform](https://github.com/coq/platform/releases). Download the installer for your OS.
2.  **Install the Extension:** Open VS Code and install the **[VsRocq](https://open-vsx.org/extension/rocq-prover/vsrocq)** extension.

## How to Run the Code

### Interactive Mode (Recommended)
1.  Open any `.lean` file (e.g., `Basics.lean`).
2.  Open the **Lean Infoview** (Click the `∀` icon in the top right).
3.  Place your cursor on any line (like `#eval` or inside a proof).
4.  The result/proof state will appear instantly in the Infoview panel.

### Batch Verification
To verify the entire project at once:

```bash
lake build
```

### Coq Workflow
**1. Interactive Mode (Line-by-Line)**
* Open any `.v` file (e.g., `Basics.v`).
* Use the **VsCoq** extension shortcuts to step through the proof:
    * **Alt + ↓ (Down Arrow):** Step forward.
    * **Alt + ↑ (Up Arrow):** Step backward.
* The proof state will appear in the side panel.

**2. Batch Build (Compiling .vo files)**
If you want to compile the files (necessary when `Induction.v` imports `Basics.v`), follow this standard workflow:

**Step A: Configure**
Ensure the file `_CoqProject` exists in the root and lists the files you want to compile:
```text
-Q . LF
Basics.v
Induction.v
```

**Step B: Generate Makefile**
Run this in your terminal:
```bash
coq_makefile -f _CoqProject -o Makefile.coq
```

**Step C: Build**
Run this to compile the `.vo` files:
```bash
make Filename.vo
```
