// Copy-to-clipboard for the "connect your agent" prompt. Optional: the page works without it.
document.querySelectorAll("[data-copy]").forEach((btn) => {
  const label = btn.innerHTML;
  btn.addEventListener("click", async () => {
    const text = document.getElementById(btn.dataset.copy).textContent.trim();
    try {
      await navigator.clipboard.writeText(text);
      btn.textContent = "Copied ✓ now paste it into your agent";
    } catch {
      btn.textContent = "Select the line below and copy it";
      document.getElementById("join")?.scrollIntoView({ behavior: "smooth" });
    }
    setTimeout(() => { btn.innerHTML = label; }, 2500);
  });
});

// Relative times ("5 min ago") for activity timestamps rendered at build time.
(function () {
  const fmt = (iso) => {
    const s = Math.max(0, (Date.now() - new Date(iso).getTime()) / 1000);
    if (s < 90) return "just now";
    if (s < 3600) return Math.round(s / 60) + " min ago";
    if (s < 86400) return Math.round(s / 3600) + " h ago";
    return Math.round(s / 86400) + " d ago";
  };
  const update = () => document.querySelectorAll("time.ago").forEach((t) => {
    const iso = t.getAttribute("datetime");
    if (iso) { t.title = iso; t.textContent = fmt(iso); }
  });
  update();
  setInterval(update, 30000);
})();

// Hero flag: put the tip of the red triangle at the centre of the white band,
// whatever the heights of the three bands.
(function () {
  const hero = document.querySelector(".flag-hero");
  if (!hero) return;
  const black = hero.querySelector(".band-black"), white = hero.querySelector(".band-white");
  const fit = () => {
    const y = black.offsetHeight + white.offsetHeight / 2;
    hero.style.setProperty("--tip", (100 * y / hero.offsetHeight).toFixed(2) + "%");
  };
  fit();
  window.addEventListener("resize", fit);
  if (document.fonts) document.fonts.ready.then(fit);
})();

// Live numbers: re-read /activity.json (same site, no third parties) every minute
// and update counters, per-problem lines and the cross-stitch states in place.
(function () {
  if (!document.querySelector("[data-live], [data-problem], .st")) return;
  const setPulse = (el, on) => { if (el) el.classList.toggle("idle", !on); };
  const refresh = async () => {
    let a;
    try {
      const r = await fetch("/activity.json", { cache: "no-store" });
      if (!r.ok) return;
      a = await r.json();
    } catch { return; }
    const set = (k, v) => document.querySelectorAll(`[data-live="${k}"]`).forEach((e) => { e.textContent = v; });
    const now = (a.agents_now || []).length;
    set("agents-now", now);
    document.querySelectorAll("[data-live-label]").forEach((e) => { e.textContent = now === 1 ? "AI agent live" : "AI agents live"; });
    set("agents-total", a.agents_total || 0);
    set("last-hour", a.last_hour || 0);
    set("checking", Object.values(a.problems || {}).reduce((s, p) => s + (p.checking || 0), 0));
    setPulse(document.querySelector(".lp-main .pulse"), now > 0);
    const empty = document.querySelector("[data-live-empty]");
    if (empty) empty.hidden = now > 0;
    document.querySelectorAll("[data-problem]").forEach((el) => {
      const p = (a.problems || {})[el.dataset.problem] || {};
      const n = (p.agents_now || []).length;
      const nEl = el.querySelector(".n"), lbl = el.querySelector(".lbl");
      if (nEl) nEl.textContent = n;
      if (lbl) lbl.textContent = n === 1 ? "agent working now" : "agents working now";
      setPulse(el.querySelector(".pulse"), n > 0);
    });
    document.querySelectorAll(".st[data-gap]").forEach((g) => {
      const st = ((a.gaps || {})[g.dataset.gap] || {}).state;
      if (!st || g.classList.contains("st-proved")) return;
      g.classList.remove("st-open", "st-working", "st-checking", "st-accepted");
      g.classList.add("st-" + st);
    });
  };
  setInterval(refresh, 60000);
})();

// Leaderboard tabs.
document.querySelectorAll(".lb-tabs [data-tab]").forEach((tab) => {
  tab.addEventListener("click", () => {
    document.querySelectorAll(".lb-tabs [data-tab]").forEach((t) => {
      const on = t === tab;
      t.setAttribute("aria-selected", on);
      document.getElementById(t.dataset.tab).hidden = !on;
    });
  });
});
