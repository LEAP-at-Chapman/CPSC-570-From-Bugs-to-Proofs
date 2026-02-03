# CPSC 570: From Bugs to Proofs

([on github](https://github.com/LEAP-at-Chapman/CPSC-570-From-Bugs-to-Proofs))

This is the repository for the course CPSC-570 From Bugs to Proof in Spring 2026.

At the end of the course, we will have written a draft of an introductory book on the use of software tools and formal reasoning to develop programs that are correct by construction.

In this course, we will learn how to write programs that are correct by construction. According to the slogan "one proof to replace 1000 test cases" this will demonstrate practical applications of logical reasoning and formal methods to concrete problems in software engineering, ranging from small individual to industry-grade projects, and supported by cutting-edge AI tools. We will use functional programming and type theory to guarantee the safety and reliability of code, based on the viewpoint that mathematical and logical proofs correspond to executable programs.

Possible languages used in this course are, for example, Python, Haskell, Lean, Dafny or others.

## Content

**Quick Links**:
- [Overview](overview.md)
- [Lecture by Lecture](lecture-by-lecture.md)
- [Canvas](https://canvas.chapman.edu/courses/83641)
- [How to create a jupyter book](docs/jupyter-books/how-to-create-a-jupyter-book.md)

**Resources on Discrete Mathematics**:
- Dr Moshier's book (see Canvas)
- My [Revision Guide: Discrete Mathematics (Logic and Relations)](https://hackmd.io/@alexhkurz/SJ1cc-dDr)
  
**Free and Open Source Books on Logic**:
- The [Open Logic Project](https://builds.openlogicproject.org/)
- P G Magnus. [An Introduction to Formal Logic](https://www.fecundity.com/logic/index.html) ... [pdf](https://www.fecundity.com/codex/forallx.pdf).
- van Benthem etal. [Logic in Action](https://www.logicinaction.org/) ... [pdf](https://www.logicinaction.org/docs/lia.pdf)
- Stephen G. Simpson. [Mathematical Logic](https://sgslogic.net/t20/notes/logic.pdf). See also his other [Lecture Notes](https://sgslogic.net/t20/notes/).

**Blogs, Videos, etc**:
- Hillel Wayne: [Logical Duals in Software Engineering](https://buttondown.com/hillelwayne/archive/logical-duals-in-software-engineering/)

## Jupyter Book

### Setup, Installation, Etc

**Quick Setup** (recommended):
```bash
./setup.sh
```

**Manual Setup**:
1. **Install dependencies**:
   ```bash
   pip install -r requirements.txt
   ```

2. **Build the book**:
   ```bash
   jupyter-book build .
   ```

3. **View the book locally**:
   ```
   open _build/html/content/0-title.html
   ```

4. **Deploy to GitHub Pages**:
   ```bash
   ghp-import -n -p -f _build/html
   ```
   This way of deploying to Github requires the following settings. In Github->Settings->Actions choose "Disable actions". In Github->Settings->Pages choose "Deploy from a branch" and then "gh-pages" as the branch.
   
5. **View the book**: TODO

**Development**:
- For development with Jupyter notebooks: `pip install -e ".[dev]"`
- Interactive examples: [Z3 Examples](z3/z3-examples.ipynb)

## Resources on Jupyter Books
- [jupyterbook.org](https://jupyterbook.org/stable/)
- Video [Jupyter Book 101](https://www.youtube.com/watch?v=lZ2FHTkyaMU) by Chris Holdgraf
- Video Course: **Build a Jupyter Book with The Turing Way**
  - Module 2.1: [Introduction to the Turing Way](https://www.youtube.com/watch?v=JyNhPfcBxTg&list=PLBxcQEfGu3Dmdo6oKg6o9V7Q_e7WSX-vu&index=2)
  - Module 2.2: [Overview of features](https://www.youtube.com/watch?v=PmxZywVwhP8&list=PLBxcQEfGu3Dmdo6oKg6o9V7Q_e7WSX-vu&index=3)
  - Module 5: [NyST, Jupyter Notebooks in Jupyter Books](https://www.youtube.com/watch?v=K2LgwSbZH_Q&list=PLBxcQEfGu3Dmdo6oKg6o9V7Q_e7WSX-vu&index=6)
  
## Examples of Online Books
- [Computational and Inferential Thinking: The Foundations of Data Science](https://inferentialthinking.com/chapters/intro.html)
- [Intermediate Quantitative Economics with Python](https://python.quantecon.org/intro.html)
- [The Turing Way](https://book.the-turing-way.org/)
- [SciKit Learn](https://inria.github.io/scikit-learn-mooc/)
- [Visualization Curriculum](https://idl.uw.edu/visualization-curriculum/intro.html)
- [Geographic Data Science with Python](https://geographicdata.science/book/intro.html)

The Lean Community has  been very active writing online books:
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Logic and Proof](https://leanprover-community.github.io/logic_and_proof/)
- [The Mechanics of Proof](https://hrmacbeth.github.io/math2001/)

