# How to create a Jupyter Book

This course uses **Jupyter Book 2** with the **MyST** document engine. All book sources live in this `book/` directory (the folder that contains `myst.yml`, `_toc.yml`, and `content/`). Configuration is in [`myst.yml`](../../myst.yml); the table of contents is in [`_toc.yml`](../../_toc.yml) (Jupyter Book v1 format, still supported).

## Basics

From the **repository root** (install dependencies and build static HTML):

```bash
./setup-book.sh
```

From the **`book/`** directory (install, then build, then open):

```bash
cd book
./setup.sh
source .venv/bin/activate
jupyter-book build --html
open _build/html/index.html
```

On Linux, use `xdg-open` instead of `open`, or paste the file path into a browser.

For a local development server with reload:

```bash
cd book
source .venv/bin/activate
jupyter-book start
```

## Publish on the web

After `jupyter-book build --html`, publish `book/_build/html` (for example with `ghp-import` from `book/requirements.txt`). From the **repository root**:

```bash
cd book && jupyter-book build --html && cd .. && ghp-import -n -p -f book/_build/html
```

See [Host your MyST Site](https://mystmd.org/guide/deployment) for other hosting options.

## Clean rebuild

```bash
cd book
rm -rf _build
jupyter-book build --html
```
