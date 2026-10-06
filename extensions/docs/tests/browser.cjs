// Optional UI smoke test: install Playwright externally, or set PLAYWRIGHT_MODULE.
const { chromium } = require(process.env.PLAYWRIGHT_MODULE || 'playwright');
const assert = require('node:assert/strict');
(async () => {
  const base = process.env.DOCS_URL || 'http://127.0.0.1:3030/';
  const browser = await chromium.launch({
    headless: true,
    ...(process.env.CHROMIUM_BIN ? { executablePath: process.env.CHROMIUM_BIN } : {})
  });
  try {
    const page = await browser.newPage({ viewport: { width: 1440, height: 1000 } });
    const errors = [];
    page.on('pageerror', error => errors.push(error.message));
    await page.goto(base);
    assert.equal(await page.locator('main > h1').textContent(), 'Library explorer');
    assert.equal(await page.locator('aside nav a').count(), 8);
    await page.locator('main .entry').filter({ hasText: 'std' }).click();
    await page.locator('main .entry').filter({ hasText: 'src' }).click();
    await page.locator('main .entry').filter({ hasText: 'root.ref' }).click();
    await page.getByRole('link', { name: 'Open module Data →', exact: true }).click();
    await page.getByRole('link', { name: 'Open module Nat →', exact: true }).click();
    assert.equal(await page.locator('main > h1').textContent(), 'Nat.ref');
    assert.match(await page.locator('.declaration').first().textContent(), /Natural numbers shared/);
    assert.match(await page.locator('.signature').first().textContent(), /succ: Nat -> Nat/);
    await page.locator('.source-link').first().click();
    assert.match(page.url(), /\/source\/\d+#L2$/);
    assert.match(await page.locator(':target').textContent(), /inductive Nat/);
    await page.getByRole('link', { name: '← Back to documentation' }).click();
    await page.locator('#filter').fill('Basic');
    assert.equal(await page.locator('[data-search]:visible').count(), 1);
    await page.locator('.toc a').filter({ hasText: /^Nat$/ }).click();
    await page.waitForFunction(() => document.querySelector('#filter').value === '');
    assert.equal(await page.locator('#filter').inputValue(), '');
    assert.equal(await page.locator('[data-search]:visible').count(), 8);
    // Re-selecting the same anchor must also clear a filter (no hashchange event).
    await page.locator('#filter').fill('Basic');
    await page.locator('.toc a').filter({ hasText: /^Nat$/ }).click();
    await page.waitForFunction(() => document.querySelector('#filter').value === '');
    if (process.env.DOCS_SCREENSHOT) await page.screenshot({ path: process.env.DOCS_SCREENSHOT, fullPage: true });
    await page.locator('#global-search').fill('quotient');
    await page.getByRole('button', { name: 'Search', exact: true }).click();
    await page.waitForURL('**/search?q=quotient');
    await page.waitForFunction(() => document.querySelector('#filter')?.value === 'quotient');
    assert.ok(await page.locator('[data-search]:visible').count() > 10);
    for (const text of await page.locator('[data-search]:visible').allTextContents()) assert.ok(text.toLowerCase().includes('quotient'));
    await page.locator('#filter').fill('UNLIKELY_NO_MATCH_932839');
    assert.equal(await page.locator('[data-search]:visible').count(), 0);
    assert.ok(await page.locator('#no-results').isVisible());
    await page.goto(base + 'search?q=%3Cscript%3Ealert(1)%3C%2Fscript%3E');
    await page.waitForFunction(() => document.querySelector('#filter')?.value.startsWith('<script>'));
    assert.equal(await page.locator('script').count(), 1);
    await page.setViewportSize({ width: 390, height: 844 });
    await page.goto(base);
    assert.ok(await page.locator('main > h1').isVisible());
    assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth));
    await page.emulateMedia({ colorScheme: 'dark' });
    assert.ok(await page.locator('main').isVisible());
    assert.deepEqual(errors, []);
    console.log('Chromium UI: navigation, module/source links, filtering, search, escaping, mobile and dark mode passed');
  } finally { await browser.close(); }
})().catch(error => { console.error(error); process.exitCode = 1; });
