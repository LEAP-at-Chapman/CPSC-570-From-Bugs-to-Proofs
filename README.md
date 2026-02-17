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

## Assessment

Assessment will be divided into a total of 200 points:

| Component               | Points |
|-------------------------|--------|
| Homework                 | 100           |    
| Book chapter |100       |                        |
| **TOTAL**               | **200**|                     

There are are 12 homework à 12 points. The total points for the homework is capped at a 100.

Instructions and guidelines for the book chapter will be released separately shortly.

## Course Grade Breakdown

Grading scale used for the course:

| Percentage | Letter |
|---|---|
| 90 |	A |
| 80-89 | 	B |
| 70-79	| C |
| 60-69	| D |
| < 60 |	F |

You must score a 70 or above to receive a P when taking the course P/NP.

## Late Policy

It is important to start working on any assignment before the deadline. For example, in case you have questions, there needs to be time to aske them in office hours. On the other hand, I want you to do good work and I am happy to give you more time if that improves the quality of your work. Here are the rules I came up with:

- If midnight approaches and you need a bit more time to finish that is not a problem as long as you submit before the sun rises.

- If you need more time than that you need to be able to convince me that you started early and already have done substantial work (for example by showing me the code in your GitHub repository). You need to send me an email explaining the special circumstances at least one day before the deadline.

I reserve the right to not grade any work that does not follow this policy.

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

## Policies required to be listed via University guidelines

#### Chapman University’s Academic Integrity Policy

Chapman University is a community of scholars that emphasizes the mutual responsibility of all members to seek knowledge honestly and in good faith.  Students are responsible for doing their own work and academic dishonesty of any kind will be subject to sanction by the instructor/administrator and referral to the university Academic Integrity Committee, which may impose additional sanctions including expulsion.  Please see the full description of Chapman University's policy on Academic Integrity.

#### Chapman University’s Students with Disabilities Policy

In compliance with ADA guidelines, students who have any condition, either permanent or temporary, that might affect their ability to perform in this class are encouraged to contact the Office of Disability Services.  If you will need to utilize your approved accommodations in this class, please follow the proper notification procedure for informing your professor(s).  This notification process must occur more than a week before any accommodation can be utilized.  Please contact Disability Services at (714) 516–4520 if you have questions regarding this procedure or for information or to make an appointment to discuss and/or request potential accommodations based on documentation of your disability.  Once formal approval of your need for an accommodation has been granted, you are encouraged to talk with your professor(s) about your accommodation options.  The granting of any accommodation will not be retroactive and cannot jeopardize the academic standards or integrity of the course.

#### Chapman University’s Equity and Diversity Policy

Chapman University is committed to ensuring equality and valuing diversity.  Students and professors are reminded to show respect at all times as outlined in Chapman’s Harassment and Discrimination Policy.  Please review the full description of Harassment and Discrimination Policy. Any violations of this policy should be discussed with the professor, the Dean of Students and/or otherwise reported in accordance with this policy.”

#### Student Support at Chapman University

Over the course of the semester, you may experience a range of challenges that interfere with your learning, such as problems with friend, family, and or significant other relationships; substance use; concerns about personal adequacy; feeling overwhelmed; or feeling sad or anxious without knowing why.  These mental health concerns or stressful events may diminish your academic performance and/or reduce your ability to participate in daily activities.  You can learn more about the resources available through Chapman University’s Student Psychological Counseling Services.

Fostering a community of care that supports the success of students is essential to the values of Chapman University.  Occasionally, you may come across a student whose personal behavior concerns or worries you, either for the student’s well-being or yours.  In these instances, you are encouraged to contact the Chapman University Student Concern Intervention Team who can respond to these concerns and offer assistance. While it is preferred that you include your contact information so this team can follow up with you, you can submit a report anonymously.  24-hour emergency help is also available through Public Safety at 714-997-6763.

#### Religious Accommodation

Religious Accommodation at Chapman University Consistent with our commitment of creating an academic community that is respectful of and welcoming to persons of differing backgrounds, we believe that every reasonable effort should be made to allow members of the university community to fulfill their obligations to the university without jeopardizing the fulfillment of their sincerely held religious obligations. Please review the syllabus early in the semester and consult with your faculty member promptly regarding any possible conflicts with major religious holidays, being as specific as possible regarding when those holidays are scheduled in advance and where those holidays constitute the fulfillment of your sincerely held religious beliefs.

#### Changes
This syllabus is subject to change. Updates will be posted on the course website.
