function setLeftBlockMonospace(text) {
    const showTrace = document.getElementById('show-trace');
    if (!showTrace) return;

    // Split lines and find max number of columns (tab-separated)
    const lines = text.split(/\r?\n/);
    let maxCols = 0;
    for (const line of lines) {
        // Count columns by splitting on tab or every 4 spaces (tab size = 4)
        const cols = line.split(/\t| {4}/).length;
        if (cols > maxCols) maxCols = cols;
    }

    // Build header line: \t1\t2\t3...
    let header = '';
    for (let i = 1; i <= maxCols; ++i) {
        header += '\t' + i;
    }

    // Escape HTML special characters
    let html = [header, ...lines].join('\n')
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;");

    // Helper to color keyword and tab after it (if present)
    function colorWithTab(keyword, color) {
        // Match keyword followed by optional tab, and wrap both
        return html.replace(
            new RegExp(`${keyword}(\\t)?`, "g"),
            (match, tab) =>
                `<span style="background:${color};">${keyword}${tab ? "<span style='background:" + color + ";'>\\t</span>" : ""}</span>`
        );
    }

    html = colorWithTab("IF", "yellow");
    html = colorWithTab("COM", "yellow");
    html = colorWithTab("ID", "orange");
    html = colorWithTab("FU1", "#00e28b");
    html = colorWithTab("FU2", "#00c0e2");
    html = colorWithTab("#sq", "red");

    // Replace literal tab characters with real tab for <pre>
    html = html.replace(/\\t/g, "\t");

    // Set tab size to 4 using CSS
    showTrace.innerHTML = `<pre style="font-family: monospace; margin: 0; tab-size: 4; -moz-tab-size: 4;">${html}</pre>`;
}

let blocks = [];
let currentBlock = 0;

function updateNavButtons() {
    const prevBtn = document.getElementById('prev-btn');
    const nextBtn = document.getElementById('next-btn');
    const frameCounter = document.getElementById('frame-counter');
    prevBtn.disabled = currentBlock <= 0;
    nextBtn.disabled = currentBlock >= blocks.length - 1;
    prevBtn.style.opacity = prevBtn.disabled ? "0.5" : "1";
    nextBtn.style.opacity = nextBtn.disabled ? "0.5" : "1";
    // Update frame counter (1-based)
    frameCounter.textContent = blocks.length > 0 ? `${currentBlock + 1}/${blocks.length}` : `0/0`;
}

document.getElementById('parse-btn').addEventListener('click', function() {
    const input = document.getElementById('input-area').value;
    // Split by two or more newlines (handles \r\n and \n)
    blocks = input.split(/(?:\r?\n){2,}/);
    currentBlock = 0;
    if (blocks.length > 0) {
        setLeftBlockMonospace(blocks[0]);
    } else {
        setLeftBlockMonospace('');
    }
    updateNavButtons();
});

document.getElementById('prev-btn').addEventListener('click', function() {
    if (currentBlock > 0) {
        currentBlock--;
        setLeftBlockMonospace(blocks[currentBlock]);
        updateNavButtons();
    }
});

document.getElementById('next-btn').addEventListener('click', function() {
    if (currentBlock < blocks.length - 1) {
        currentBlock++;
        setLeftBlockMonospace(blocks[currentBlock]);
        updateNavButtons();
    }
});

// Handle left/right arrow keys for prev/next navigation
document.addEventListener('keydown', function(e) {
    // Ignore if focus is in textarea or input
    const active = document.activeElement;
    if (active && (active.tagName === 'TEXTAREA' || active.tagName === 'INPUT')) return;

    if (e.key === 'ArrowLeft') {
        const prevBtn = document.getElementById('prev-btn');
        if (!prevBtn.disabled) {
            prevBtn.click();
            e.preventDefault();
        }
    } else if (e.key === 'ArrowRight') {
        const nextBtn = document.getElementById('next-btn');
        if (!nextBtn.disabled) {
            nextBtn.click();
            e.preventDefault();
        }
    }
});