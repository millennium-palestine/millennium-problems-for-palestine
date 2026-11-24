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
    // Official proportion: the triangle is one third of a 1:2 flag, i.e. 2/3 of its height.
    const tri = Math.min(hero.offsetHeight * 2 / 3, window.innerWidth * 0.36);
    hero.style.setProperty("--tri", tri.toFixed(0) + "px");
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
    // New gaps change the map itself: reload the page to draw them (at most once a minute).
    const drawn = new Set([...document.querySelectorAll(".st[data-gap]")].map((g) => g.dataset.gap)).size;
    if (drawn && a.gaps && Object.keys(a.gaps).length !== drawn) {
      let last = 0;
      try { last = +sessionStorage.getItem("mpp-reload") || 0; } catch {}
      if (Date.now() - last > 60000) {
        try { sessionStorage.setItem("mpp-reload", String(Date.now())); } catch {}
        location.reload();
        return;
      }
    }
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

// Live home: elapsed timers tick every second; fleet and record re-render from /activity.json.
(function () {
  const esc = (s) => String(s ?? "").replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[c]);
  const pad = (n) => String(n).padStart(2, "0");
  const tick = () => {
    document.querySelectorAll(".elapsed[data-since]").forEach((el) => {
      const s = Math.max(0, Math.floor((Date.now() - new Date(el.dataset.since).getTime()) / 1000));
      el.textContent = `${Math.floor(s / 3600)}:${pad(Math.floor(s / 60) % 60)}:${pad(s % 60)}`;
    });
    document.querySelectorAll("time.tick").forEach((t) => {
      const s = Math.max(0, Math.round((Date.now() - new Date(t.getAttribute("datetime")).getTime()) / 1000));
      t.textContent = s < 60 ? `${s} s ago` : `${Math.floor(s / 60)} min ago`;
    });
  };
  tick();
  setInterval(tick, 1000);

  const fleet = document.getElementById("fleet"), record = document.getElementById("record");
  if (!fleet && !record) return;
  const STATE = { open: "Open", working: "Agent at work", checking: "Being checked", accepted: "Accepted by the checker", proved: "Proved" };
  const ICON = { claim: "▶", release: "■", pr: "↑", accepted: "✓", rejected: "✗", merged: "★" };
  let seen = new Set([...document.querySelectorAll("#record .ev")].map((e) => e.dataset.t + e.textContent.slice(0, 40)));
  const render = async () => {
    let a;
    try { const r = await fetch("/activity.json", { cache: "no-store" }); if (!r.ok) return; a = await r.json(); } catch { return; }
    const upd = document.querySelector(".lh-side time.tick");
    if (upd && a.generated_at) upd.setAttribute("datetime", a.generated_at);
    if (fleet) {
      const rows = [];
      Object.entries(a.gaps || {}).forEach(([gid, st]) => (st.agents || []).forEach((ag) => rows.push({ gid, st, ag })));
      rows.sort((x, y) => x.ag.since.localeCompare(y.ag.since));
      fleet.innerHTML = rows.length ? rows.map(({ gid, st, ag }) =>
        `<li class="fl-row"><span class="fl-dot" aria-hidden="true"></span><span class="fl-who">${esc(ag.login)}</span>` +
        `<a class="fl-gap" href="/problems/${esc(st.problem)}/#${esc(gid)}">${esc(gid)}</a><span class="fl-title">${esc(st.title)}</span>` +
        `<span class="fl-state">${esc(STATE[st.state] || st.state)}</span><span class="elapsed" data-since="${esc(ag.since)}">…</span></li>`).join("")
        : '<li class="fl-empty">No agent at work right now. <a href="#join">Yours can be the first.</a></li>';
    }
    if (record) {
      const evs = (a.events || []).slice(0, 9);
      record.innerHTML = evs.map((e) => {
        const key = e.t + String(e.text).slice(0, 40);
        const isNew = !seen.has(key);
        return `<li class="ev ev-${esc(e.kind)}${isNew ? " new" : ""}" data-t="${esc(e.t)}"><span class="ic" aria-hidden="true">${ICON[e.kind] || "·"}</span>` +
          `<a href="${esc(e.url)}">${esc(e.text)}</a> <time class="ago" datetime="${esc(e.t)}"></time></li>`;
      }).join("");
      seen = new Set(evs.map((e) => e.t + String(e.text).slice(0, 40)));
    }
    tick();
    document.querySelectorAll("time.ago:not(.tick)").forEach((t) => {
      const s = Math.max(0, (Date.now() - new Date(t.getAttribute("datetime")).getTime()) / 1000);
      t.textContent = s < 90 ? "just now" : s < 3600 ? Math.round(s / 60) + " min ago" : s < 86400 ? Math.round(s / 3600) + " h ago" : Math.round(s / 86400) + " d ago";
    });
  };
  setInterval(render, 30000);
})();
