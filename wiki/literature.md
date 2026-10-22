# Literature

## 1. How to use the literature collection

Use the `literature` and `wiki` locations in `paths`. Open
`literature/_central-library-pointers.md` and browse the ordinary documents and
publication folders beside it. Reuse an existing source before acquiring another
copy. The directory map also identifies the authorized read-only Central-Library
when it is available; search it with ordinary native file tools.

Keep a central source where it is. A pointer may name one PDF or a publication
folder containing the PDF, TeX, bibliography, and figures. Put newly acquired
material in `.private/downloads/` in your workspace, then register it with
`copy: true` to retain it in the project literature folder under a descriptive
author/title name. Do not edit coordinator-owned literature files directly.

Coordination names below are operations called through
`taskhub_call(operation=..., arguments=...)`; obtain a needed schema with
`taskhub_actions(operation=...)`.

Exploratory reading needs no registration. When a source will be cited or is needed
to resolve a literature request, call `literature_register` with a stable
`source_id`, `title`, and the actual file or publication-folder `path`:

- Omit `copy` for a pointer to Central-Library or another retained source.
- Use `copy: true` to import a downloaded file or folder from your workspace.
  The coordinator retains a readable local name and appends its pointer entry.
- Supply the edition/version, original URL, and bibliographic citation when known.
  Reuse the returned ID and fingerprint; do not register the same source twice.
  Registering an already recorded, unchanged ID/title/path returns its existing
  citation receipt; omitted optional metadata does not erase it.

The single Markdown index is the browsing entry point. Fingerprints and citation
receipts are internal bookkeeping; do not maintain them by hand. Preserve existing
entries and other workers' notes. A changed edition needs a new source ID. To cite
a folder, identify the actual file as well as its page, section, definition, or
theorem in the locator. Internal references to retained local copies are relative
to the project; Central-Library pointers remain local external references.

## 2. Missing literature

If the exact source is still unavailable, call `request` with `kind: "literature"`,
a stable `request_key` identifying the work and edition, `title`, and `text`.
The same source/version key can join waiters across tasks only when the exact
title and text agree. Reusing it with incompatible content fails explicitly;
use a distinct key for a different source, edition, or request.
The user's project page shows
the request. Continue independent work when possible; otherwise checkpoint and
wait on the returned external-response predicate. Human requests are not tasks
for another newly spawned worker.

A supplied URL is a lead, not fulfillment. After the actual file or folder is
accessible, register it and resolve the request with `request_resolve`.
All attached waiters receive the result. Never invent a missing source or claim
that a declined request made it available. A worker's fulfillment response remains
worker correspondence; only trusted `sender_role: "operator"`
carries human authority. Verify the actual source and request state before relying
on a response, and never treat it as permission to bypass publication checks.
Read each complete response file at `messages[].file.path` before acting on it.
Transport receipt is not comprehension; send no extra read acknowledgment. Completed
responses are immutable; a correction uses a new request when further human
input is needed. The dashboard validates a response before importing its exact
content-bound local copy, so rejected form input cannot register a source.

## 3. Citations and review

Mathematical records cite `literature_id`, the exact `content_sha256`, and a precise
locator. Paired Markdown identifies the same source and location. Read the cited
original, rather than relying only on a summary, title, or abstract.

For definitions and proposition statements, verify agreement among original
literature, Lean, and Markdown, including hypotheses, quantifiers, conventions,
and scope. For proofs, check the implemented Lean proof, its Markdown explanation,
and exact dependencies; a different valid proof route is permitted. Record concrete
correspondence findings. Compilation alone does not establish faithful translation.

Central-Library remains read-only. Registering or copying literature is acquisition,
not mathematical approval. Local pointers do not make a source available on another
machine, and access to a source does not imply permission to publish its contents.

## Native downloads

Network access is enabled in the worker sandbox. Download into
`.private/downloads/` in your workspace, then use `literature_register` with the
local file and source details. Search the project literature and central collection
first. A discovered URL alone is not a retained source.

On Windows, if curl fails with `SEC_E_NO_CREDENTIALS` or another Schannel error,
use the Python executable in `TASKBASED_PYTHON` with `urllib.request.urlretrieve`.
This uses OpenSSL and preserves HTTPS verification. Do not disable TLS checks.
Request human assistance only when the source is still inaccessible, for example
a paywall or missing edition; include the exact citation and attempted locations.
