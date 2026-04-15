# How to create a Jupyter Book

This course uses **Jupyter Book 2** with the **MyST** document engine. All book sources live in this `book/` directory (the folder that contains `myst.yml`, `_toc.yml`, and `content/`). Configuration is in [`myst.yml`](../../myst.yml); the table of contents is in [`_toc.yml`](../../_toc.yml) (Jupyter Book v1 format, still supported).

## Basics

From the **repository root** (install, build, then serve the static site):

```bash
./setup-book.sh
./serve-book.sh
```

Then open **http://localhost:8844/** and leave `serve-book.sh` running. **`ERR_CONNECTION_REFUSED`** means no server is listening on that port (start `./serve-book.sh` first, or you closed it while the tab was still loading).

From the **`book/`** directory (install, build, live dev server):

```bash
cd book
./setup.sh
source .venv/bin/activate
jupyter-book build --html
jupyter-book start
```

Do **not** rely on double-clicking `index.html` or using `file://` URLs: MyST uses root-absolute paths such as `/build/...`, which break under `file://`. See [Custom domains and the base URL](https://mystmd.org/guide/deployment#deploy-base-url).

On Linux, use `xdg-open` with a real `http://` URL if you open a browser from the terminal.

## GitHub Pages

For `https://<org>.github.io/<repo>/`, set `BASE_URL=/repo` when building (this repository: `/CPSC-570-From-Bugs-to-Proofs`). From the **repository root**:

```bash
./book/scripts/build-github-pages.sh
```

## Publish on the web

After a `BASE_URL`-aware build, publish `book/_build/html` (for example with `ghp-import` from `book/requirements.txt`). From the **repository root**:

```bash
./book/scripts/build-github-pages.sh
ghp-import -n -p -f book/_build/html
```

See [Host your MyST Site](https://mystmd.org/guide/deployment) for other hosting options.

## Clean rebuild

```bash
cd book
rm -rf _build
source .venv/bin/activate
jupyter-book build --html
```
