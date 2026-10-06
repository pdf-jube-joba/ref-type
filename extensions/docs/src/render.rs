use crate::catalog::Catalog;
use pulldown_cmark::{Event, Options, Parser, Tag, TagEnd, html};
use std::{collections::HashMap, fmt::Write, path::Path};
use syntax::parse::documentation::DocumentationItem;

pub fn escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for ch in text.chars() {
        out.push_str(match ch {
            '&' => "&amp;",
            '<' => "&lt;",
            '>' => "&gt;",
            '"' => "&quot;",
            '\'' => "&#39;",
            _ => {
                out.push(ch);
                continue;
            }
        });
    }
    out
}

fn label(path: &Path) -> String {
    path.file_name()
        .map_or_else(|| "libs".into(), |name| name.to_string_lossy().into_owned())
}

fn page(c: &Catalog, title: &str, directory: usize, body: &str) -> String {
    let mut nav = String::new();
    for &id in &c.directories[0].directories {
        let _ = write!(
            nav,
            "<a href=\"/dir/{id}\">{}</a>",
            escape(&label(&c.directories[id].path))
        );
    }
    let mut crumbs = Vec::new();
    let mut current = Some(directory);
    while let Some(id) = current {
        crumbs.push(format!(
            "<a href=\"/dir/{id}\">{}</a>",
            escape(&label(&c.directories[id].path))
        ));
        current = c.directories[id].parent;
    }
    crumbs.reverse();
    format!(
        r#"<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1"><title>{title} · Ref Type docs</title><link rel="stylesheet" href="/style.css"><script src="/app.js" defer></script></head><body><header><a class="brand" href="/">Ref Type <span>library docs</span></a><form action="/search" role="search"><label class="sr-only" for="global-search">Search libraries</label><input id="global-search" name="q" type="search" placeholder="Search declarations and docs…"><button>Search</button></form></header><div class="layout"><aside><p class="eyebrow">LIBRARIES</p><nav aria-label="Libraries">{nav}</nav><a class="search-link" href="/search">All declarations →</a><p class="aside-note">Source signatures<br>Local library snapshot</p></aside><main><nav class="breadcrumbs" aria-label="Breadcrumb">{crumbs}</nav>{body}<footer>Ref Type documentation · Restart the server to reload changes.</footer></main></div></body></html>"#,
        title = escape(title),
        crumbs = crumbs.join("<span>/</span>")
    )
}

pub fn directory(c: &Catalog, id: usize) -> String {
    let dir = &c.directories[id];
    let title = if id == 0 {
        "Library explorer".into()
    } else {
        dir.path.display().to_string()
    };
    let mut body = format!(
        "<p class=\"eyebrow\">DIRECTORY</p><h1>{}</h1><p class=\"muted\">{} directories · {} source files</p>",
        escape(&title),
        dir.directories.len(),
        dir.files.len()
    );
    if id == 0 {
        let _ = write!(
            body,
            "<p>Browse mathematical libraries, read declaration signatures and follow proofs in their source. <strong>{} source files</strong> indexed.</p>",
            c.files.len()
        );
    }
    body.push_str("<div class=\"entries\">");
    for &child in &dir.directories {
        let _ = write!(
            body,
            "<a class=\"entry\" href=\"/dir/{child}\"><span class=\"badge\">dir</span> {} <span aria-hidden=\"true\">→</span></a>",
            escape(&label(&c.directories[child].path))
        );
    }
    for &child in &dir.files {
        let file = &c.files[child];
        let _ = write!(
            body,
            "<a class=\"entry\" href=\"/file/{child}\"><span class=\"badge\">ref</span> {} <small>{} declarations{}</small></a>",
            escape(&label(&file.path)),
            file.items.len(),
            if file.error.is_some() {
                " · parse error"
            } else {
                ""
            }
        );
    }
    body.push_str("</div>");
    if dir.files.is_empty() && dir.directories.is_empty() {
        body.push_str("<p class=\"empty\">No .ref files or subdirectories in this directory.</p>");
    }
    if let Some(readme) = &dir.readme {
        body.push_str("<section class=\"readme\" id=\"readme\"><h2>README</h2>");
        body.push_str(&markdown(c, &dir.path, readme));
        body.push_str("</section>");
    }
    page(c, &title, id, &body)
}

pub fn file(c: &Catalog, id: usize) -> String {
    let file = &c.files[id];
    let mut body = format!(
        "<p class=\"eyebrow\">SOURCE MODULE</p><h1>{}</h1><p><a href=\"/source/{id}\">View source with line numbers →</a></p><p class=\"muted\">Signatures preserve source notation. Implicit types (_) are shown as written.</p>",
        escape(&label(&file.path))
    );
    if let Some(error) = &file.error {
        let _ = write!(
            body,
            "<p class=\"error\">Could not parse this file: {}. The complete source is still available.</p>",
            escape(error)
        );
    } else if file.items.is_empty() {
        body.push_str("<p class=\"empty\">No named declarations. This file may be empty or contain only comments or commands; see its source.</p>");
    } else {
        body.push_str("<label class=\"filter-label\" for=\"filter\">Filter this module</label><input id=\"filter\" type=\"search\" placeholder=\"Name, type or documentation\"><p id=\"result-count\" class=\"muted\" aria-live=\"polite\"></p><nav class=\"toc\" aria-label=\"Declarations\">");
        toc(&file.items, "", &mut body);
        body.push_str("</nav>");
        let stem = file.path.file_stem().unwrap_or_default();
        let mut module_path = file.path.parent().unwrap_or(Path::new("")).to_path_buf();
        if stem != "root" {
            module_path.push(stem);
        }
        items(c, id, &file.items, "", &module_path, &mut body);
        body.push_str(
            "<p id=\"no-results\" class=\"empty\" hidden>No declarations match your search.</p>",
        );
    }
    page(c, &file.path.display().to_string(), file.directory, &body)
}

fn toc(items: &[DocumentationItem], prefix: &str, out: &mut String) {
    for item in items {
        let name = format!("{prefix}{}", item.name);
        let _ = write!(
            out,
            "<a href=\"#d{}\">{}</a>",
            item.span.start,
            escape(&name)
        );
        toc(&item.children, &format!("{name}."), out);
    }
}

fn items(
    c: &Catalog,
    id: usize,
    declarations: &[DocumentationItem],
    prefix: &str,
    module_path: &Path,
    out: &mut String,
) {
    let file = &c.files[id];
    for item in declarations {
        let name = format!("{prefix}{}", item.name);
        let line = file.text[..item.span.start]
            .bytes()
            .filter(|&b| b == b'\n')
            .count()
            + 1;
        let _ = write!(
            out,
            "<article class=\"declaration\" data-search id=\"d{}\"><div class=\"declaration-heading\"><span class=\"badge\">{}</span><h2><a href=\"#d{}\">{}</a></h2><a class=\"source-link\" href=\"/source/{id}#L{line}\">source:{line}</a></div><pre class=\"signature\"><code>{}</code></pre>",
            item.span.start,
            item.kind,
            item.span.start,
            escape(&name),
            escape(&item.signature)
        );
        if item.documentation.is_empty() {
            out.push_str("<p class=\"undocumented\">No documentation comment.</p>");
        } else {
            out.push_str(&format!(
                "<div class=\"prose\">{}</div>",
                markdown_with_prefix(
                    c,
                    file.path.parent().unwrap_or(Path::new("")),
                    &item.documentation,
                    &format!("d{}-", item.span.start)
                )
            ));
        }
        let child_path = module_path.join(&item.name);
        if item.external {
            if let Some(link) = c.links.get(&child_path.with_extension("ref")) {
                let _ = write!(
                    out,
                    "<a class=\"module-link\" href=\"{link}\">Open module {} →</a>",
                    escape(&name)
                );
            } else {
                out.push_str("<p class=\"muted\">External module source is not present in this library snapshot.</p>");
            }
        }
        out.push_str("</article>");
        items(c, id, &item.children, &format!("{name}."), &child_path, out);
    }
}

pub fn source(c: &Catalog, id: usize) -> String {
    let file = &c.files[id];
    let mut body = format!(
        "<p class=\"eyebrow\">SOURCE</p><h1>{}</h1><p><a href=\"/file/{id}\">← Back to documentation</a></p><pre class=\"source\"><code>",
        escape(&file.path.display().to_string())
    );
    for (index, line) in file.text.lines().enumerate() {
        let n = index + 1;
        let _ = writeln!(
            body,
            "<span class=\"source-line\" id=\"L{n}\"><a class=\"line-number\" href=\"#L{n}\" aria-label=\"Line {n}\">{n}</a>{}</span>",
            escape(line)
        );
    }
    body.push_str("</code></pre>");
    page(c, &file.path.display().to_string(), file.directory, &body)
}

pub fn search(c: &Catalog) -> String {
    let mut body = String::from(
        "<p class=\"eyebrow\">ALL LIBRARIES</p><h1>Find a declaration</h1><label class=\"filter-label\" for=\"filter\">Search names, modules, signatures and comments</label><input id=\"filter\" type=\"search\" placeholder=\"For example: Nat, continuity, quotient…\"><p id=\"result-count\" aria-live=\"polite\" class=\"muted\"></p><noscript>Use your browser’s Find command to search this index.</noscript><div class=\"search-results\">",
    );
    for (id, file) in c.files.iter().enumerate() {
        let _ = write!(
            body,
            "<a class=\"entry\" data-search href=\"/file/{id}\"><span class=\"badge\">file</span>{}</a>",
            escape(&file.path.display().to_string())
        );
        search_items(&file.items, id, &file.path.display().to_string(), &mut body);
    }
    body.push_str(
        "</div><p id=\"no-results\" class=\"empty\" hidden>No declarations match your search.</p>",
    );
    page(c, "Search", 0, &body)
}

fn search_items(items: &[DocumentationItem], id: usize, prefix: &str, out: &mut String) {
    for item in items {
        let name = format!("{prefix} · {}", item.name);
        let _ = write!(
            out,
            "<a class=\"search-result\" data-search href=\"/file/{id}#d{}\"><span class=\"badge\">{}</span><strong>{}</strong><code>{}</code><span class=\"search-doc\">{}</span></a>",
            item.span.start,
            item.kind,
            escape(&name),
            escape(&item.signature),
            escape(&item.documentation)
        );
        search_items(&item.children, id, &name, out);
    }
}

pub fn markdown(c: &Catalog, base: &Path, text: &str) -> String {
    markdown_with_prefix(c, base, text, "md-")
}

fn markdown_with_prefix(c: &Catalog, base: &Path, text: &str, prefix: &str) -> String {
    let text = preserve_math(text);
    let parser = Parser::new_ext(
        &text,
        Options::ENABLE_TABLES | Options::ENABLE_STRIKETHROUGH,
    );
    let events: Vec<_> = parser.collect();
    let mut heading = String::new();
    let mut in_heading = false;
    let mut counts = HashMap::new();
    let mut headings = Vec::new();
    for event in &events {
        match event {
            Event::Start(Tag::Heading { .. }) => {
                in_heading = true;
                heading.clear();
            }
            Event::Text(text) | Event::Code(text) if in_heading => heading.push_str(text),
            Event::End(TagEnd::Heading(_)) => {
                in_heading = false;
                let slug: String = heading
                    .to_lowercase()
                    .chars()
                    .filter(|ch| {
                        ch.is_alphanumeric() || ch.is_whitespace() || *ch == '-' || *ch == '_'
                    })
                    .map(|ch| if ch.is_whitespace() { '-' } else { ch })
                    .collect();
                let count = counts.entry(slug.clone()).or_insert(0);
                headings.push(if *count == 0 {
                    format!("{prefix}{slug}")
                } else {
                    format!("{prefix}{slug}-{count}")
                });
                *count += 1;
            }
            _ => {}
        }
    }
    let mut headings = headings.into_iter();
    let mut link_stack = Vec::new();
    let events = events.into_iter().filter_map(|event| match event {
        Event::Start(Tag::Heading { level, .. }) => Some(Event::Html(
            format!(
                "<{level} id=\"{}\">",
                escape(&headings.next().unwrap_or_default())
            )
            .into(),
        )),
        // Raw HTML is displayed as text, never passed through to the browser.
        Event::Html(text) | Event::InlineHtml(text) => Some(Event::Text(text)),
        Event::Start(Tag::Link {
            dest_url, title, ..
        }) => {
            let link = if let Some(fragment) = dest_url.strip_prefix('#') {
                Some(format!("#{prefix}{fragment}"))
            } else {
                c.link(base, &dest_url)
            };
            link_stack.push(link.is_some());
            link.map(|url| {
                Event::Html(
                    format!(
                        "<a href=\"{}\" title=\"{}\" rel=\"noreferrer noopener\">",
                        escape(&url),
                        escape(&title)
                    )
                    .into(),
                )
            })
        }
        Event::End(TagEnd::Link) => link_stack
            .pop()
            .unwrap_or(false)
            .then(|| Event::Html("</a>".into())),
        // Keep image alt text, without external requests or embedded image data.
        Event::Start(Tag::Image { .. }) | Event::End(TagEnd::Image) => None,
        other => Some(other),
    });
    let mut out = String::new();
    html::push_html(&mut out, events);
    out
}

/// Keep TeX delimiters and contents literal. Code spans protect backslashes,
/// underscores and asterisks from Markdown without requiring a remote renderer.
fn preserve_math(input: &str) -> String {
    let mut code = Vec::new();
    let mut block_start = 0;
    for (event, range) in Parser::new(input).into_offset_iter() {
        match event {
            Event::Code(_) => code.push(range),
            Event::Start(Tag::CodeBlock(_)) => block_start = range.start,
            Event::End(TagEnd::CodeBlock) => code.push(block_start..range.end),
            _ => {}
        }
    }
    let mut result = String::new();
    let mut cursor = 0;
    while let Some(relative) = input[cursor..].find('\\') {
        let start = cursor + relative;
        result.push_str(&input[cursor..start]);
        let closing = if input[start..].starts_with(r"\(") {
            Some(r"\)")
        } else if input[start..].starts_with(r"\[") {
            Some(r"\]")
        } else {
            None
        };
        if let Some(closing) = closing.filter(|_| !code.iter().any(|range| range.contains(&start)))
            && let Some(end) = input[start + 2..].find(closing)
        {
            let end = start + 2 + end + 2;
            let math = &input[start..end];
            let fence = "`".repeat(math.split(|c| c != '`').map(str::len).max().unwrap_or(0) + 1);
            let _ = write!(result, "{fence} {math} {fence}");
            cursor = end;
            continue;
        }
        result.push('\\');
        cursor = start + 1;
    }
    result.push_str(&input[cursor..]);
    result
}
