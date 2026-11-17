"use strict";

const field = id => document.getElementById(id);

async function showCases() {
    const response = await fetch("./cases.json");
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    const { revision, cases } = await response.json();
    const selector = field("case");
    for (const [index, example] of cases.entries()) {
        selector.add(new Option(example.title, String(index)));
    }

    function render() {
        const example = cases[Number(selector.value)];
        field("fixture").textContent = example.title;
        field("explanation").textContent = example.summary;
        field("actual").textContent = example.actual;
        field("reference").textContent = example.reference;
        field("smt").textContent = example.input;
        field("source").href = `https://github.com/Aneesh495/axiom/blob/${revision}/tests/${example.path}`;
        field("commands").textContent = `git checkout ${revision}\nswift run axiom tests/${example.path} --model\nz3 tests/${example.path}`;
        const agree = example.actual.split("\n")[0] === example.reference;
        field("status").textContent = agree ? "Recorded decisions agree." : "Recorded decisions disagree. Inspect the outputs before relying on this result.";
        field("status").classList.toggle("disagreement", !agree);
    }

    selector.addEventListener("change", render);
    selector.disabled = false;
    field("report").hidden = false;
    render();
}

showCases().catch(() => {
    field("status").textContent = "The recorded results could not load. Reload the page to try again.";
});
