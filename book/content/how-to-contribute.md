# How to contribute

From the **repository root**, run `./setup-book.sh` to install dependencies into `book/.venv` and build HTML to `book/_build/html/`. Preview with **`./serve-book.sh`** (then open http://localhost:8844/) or `jupyter-book start` from `book/`; do not use `file://` on `index.html`. If the browser shows **ERR_CONNECTION_REFUSED**, start `./serve-book.sh` and keep that terminal open. For install, build, and Git workflow hints, run `./book/scripts/student-book-setup.sh` (or `./scripts/student-book-setup.sh`).

## Writing

- Prefer short paragraphs and many **inline links** to documentation, tutorials, and primary sources.
- Avoid long code listings without explanation; introduce each block with what the reader should notice.
- When you add notebooks under `book/content/`, keep execution lightweight or ask the instructor before adding heavy dependencies.

## Layout

- Follow the [chapter outline](0-chapter-outline.md) so the book stays aligned with the course structure.
- Use multiple subsections under each major heading where appropriate (avoid a single lonely subsection).
- Link to other chapters with **relative** paths, for example `[Dafny](05-dafny.md)`.

## Pull requests

- Coordinate with your assigned reviewer ([Chapter assignments](0-chapter-assignments.md)).
- One focused pull request per chapter (or per logical chunk) is easier to review than a very large diff.

## References

See [How to cite](how-to-cite.md) for BibTeX and in-text citations.
