const filter = document.querySelector('#filter');
if (filter) {
  const entries = [...document.querySelectorAll('[data-search]')].map(element => ({
    element, text: element.textContent.toLocaleLowerCase()
  }));
  const count = document.querySelector('#result-count');
  const empty = document.querySelector('#no-results');
  const apply = () => {
    const terms = filter.value.trim().toLocaleLowerCase().split(/\s+/).filter(Boolean);
    let visible = 0;
    for (const entry of entries) {
      entry.element.hidden = !terms.every(term => entry.text.includes(term));
      if (!entry.element.hidden) visible++;
    }
    count.textContent = `${visible} / ${entries.length} results`;
    empty.hidden = visible !== 0;
  };
  filter.value = new URLSearchParams(location.search).get('q') || '';
  filter.addEventListener('input', apply);
  // A table-of-contents or search-result link must remain usable after filtering.
  const reveal = () => {
    const target = document.getElementById(location.hash.slice(1));
    if (target?.matches('[data-search]')) {
      filter.value = '';
      apply();
      target.scrollIntoView();
    }
  };
  window.addEventListener('hashchange', reveal);
  document.querySelector('.toc')?.addEventListener('click', event => {
    if (event.target.closest('a[href^="#"]')) {
      filter.value = '';
      apply();
    }
  });
  apply();
  reveal();
}
