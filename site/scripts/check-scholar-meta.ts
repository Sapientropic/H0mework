// Verify Google Scholar Highwire Press inclusion rules on every built paper page in dist/.
import assert from "node:assert/strict";
import { existsSync, readFileSync, statSync } from "node:fs";
import { resolve } from "node:path";
import { PAPERS, paperOf } from "../src/lib/papers";

const dist = resolve(process.cwd(), "dist");

function metaContent(head: string, name: string) {
  const m = head.match(new RegExp(`<meta\\s+name="${name}"\\s+content="([^"]*)"`, "i"));
  return m?.[1]?.trim() ?? "";
}

for (const entry of PAPERS) {
  for (const lang of ["zh", "en"] as const) {
    const prefix = lang === "en" ? "/en" : "";
    const pageDir = `${prefix}/papers/${entry.slug}/`;
    const htmlPath = resolve(dist, pageDir.slice(1), "index.html");
    assert.ok(existsSync(htmlPath), `Missing built HTML: ${htmlPath}`);
    const html = readFileSync(htmlPath, "utf8");
    const headEnd = html.indexOf("</head>");
    assert.ok(headEnd > 0, `${pageDir}: malformed HTML head/body`);
    const head = html.slice(0, headEnd);
    const body = html.slice(headEnd + 7);

    const title = metaContent(head, "citation_title");
    const author = metaContent(head, "citation_author");
    const pubDate = metaContent(head, "citation_publication_date");
    const pdfUrl = metaContent(head, "citation_pdf_url");
    const doi = metaContent(head, "citation_doi");

    assert.ok(title.length > 0, `${pageDir}: empty citation_title`);
    assert.ok(author.length > 0, `${pageDir}: empty citation_author`);
    assert.match(pubDate, /^\d{4}\/\d{2}\/\d{2}$/, `${pageDir}: invalid citation_publication_date ${pubDate}`);
    assert.match(doi, /^10\.5281\/zenodo\.\d+$/, `${pageDir}: invalid citation_doi ${doi}`);

    // Rule 1: citation_pdf_url must sit in the same subdirectory (or child) as the abstract HTML page.
    const expectedPrefix = `https://h0mework.wiki${pageDir}`;
    assert.ok(
      pdfUrl.startsWith(expectedPrefix) && pdfUrl.endsWith(".pdf"),
      `${pageDir}: citation_pdf_url (${pdfUrl}) is outside page subdirectory (${expectedPrefix})`,
    );

    // Rule 2: PDF file must exist in dist/, be valid %PDF-, and stay under 5 MB.
    const relPdf = new URL(pdfUrl).pathname.slice(1);
    const pdfFile = resolve(dist, relPdf);
    assert.ok(existsSync(pdfFile), `${pageDir}: missing PDF file ${pdfFile}`);
    const pdfSize = statSync(pdfFile).size;
    assert.ok(pdfSize > 10_000 && pdfSize < 5 * 1024 * 1024, `${pageDir}: PDF size out of Scholar range: ${pdfSize}`);
    assert.equal(readFileSync(pdfFile).subarray(0, 5).toString("ascii"), "%PDF-", `${pageDir}: invalid PDF header`);

    // Rule 3: Visible body must display the author name, publication date, direct PDF link, and unfolded abstract.
    const paper = paperOf(entry.slug, lang);
    assert.ok(body.includes(paper.citation.authorName), `${pageDir}: visible body missing author ${paper.citation.authorName}`);
    assert.ok(body.includes(paper.current.date), `${pageDir}: visible body missing publication date ${paper.current.date}`);
    assert.ok(body.includes(`href="${paper.citation.pdfPath}"`), `${pageDir}: visible body missing direct link to ${paper.citation.pdfPath}`);
    const abstractSection = body.match(/<div class="prose abstract">([\s\S]*?)<\/section>/)?.[1] ?? "";
    assert.ok(abstractSection.length > 0 && !abstractSection.includes("<details"), `${pageDir}: abstract must be fully visible without <details>`);

    // Rule 4: Valid Schema.org ScholarlyArticle JSON-LD linking DOI, ORCID, PDF MediaObject, and Lean 4 repository.
    const ldRaw = head.match(/<script type="application\/ld\+json">([\s\S]*?)<\/script>/)?.[1] ?? "";
    assert.ok(ldRaw.length > 0, `${pageDir}: missing application/ld+json`);
    const ld = JSON.parse(ldRaw);
    assert.equal(ld["@type"], "ScholarlyArticle", `${pageDir}: JSON-LD must be ScholarlyArticle`);
    assert.equal(ld.isAccessibleForFree, true, `${pageDir}: JSON-LD must set isAccessibleForFree=true`);
    assert.equal(ld.encoding?.contentUrl, pdfUrl, `${pageDir}: JSON-LD encoding.contentUrl mismatch`);
    assert.ok(Array.isArray(ld.sameAs) && ld.sameAs.includes(`https://doi.org/${doi}`), `${pageDir}: JSON-LD sameAs missing DOI URL`);
  }
}

console.log(`Google Scholar compliance verified across ${PAPERS.length * 2} paper pages and PDFs`);
