// Debug event type detection
const fs = require('fs');
const { WaveformToSVAGenerator } = require('./out/svaGenerator.js');

const testJson = `{
  "signal": [
    { "name": "req",   "wave": "01..0.", "node": ".a..b." },
    { "name": "ack",   "wave": "0.1.0.", "node": "..c.d." },
    { "name": "data",  "wave": "x.==.x", "node": "..e.f." }
  ],
  "edge": [
    "a~>c", "c->e", "b-|>d"
  ]
}`;

console.log('=== Event Type Detection Debug ===');

const data = JSON.parse(testJson);

// Manual event type analysis
data.signal.forEach(signal => {
    if (!signal.node) return;
    
    console.log(`\nSignal: ${signal.name}`);
    console.log(`Wave:   ${signal.wave}`);
    console.log(`Node:   ${signal.node}`);
    
    for (let i = 0; i < signal.node.length; i++) {
        const char = signal.node[i];
        if (char !== '.' && char !== '') {
            const current = signal.wave[i];
            const previous = i > 0 ? signal.wave[i - 1] : '';
            
            let eventType = 'default';
            
            if (i === 0 || i >= signal.wave.length) {
                eventType = 'default';
            } else {
                // Rising edge: 0->1, l->h, L->H
                if ((previous === '0' && current === '1') ||
                    (previous === 'l' && current === 'h') ||
                    (previous === 'L' && current === 'H')) {
                    eventType = 'rising_edge';
                }
                // Falling edge: 1->0, h->l, H->L
                else if ((previous === '1' && current === '0') ||
                    (previous === 'h' && current === 'l') ||
                    (previous === 'H' && current === 'L')) {
                    eventType = 'falling_edge';
                }
                // Data change: x->= or =->x or =->= (different data)
                else if (current === '=' || previous === '=') {
                    eventType = 'data_change';
                }
                // Stable: same value
                else if (current === previous) {
                    eventType = 'stable';
                }
            }
            
            console.log(`  Node '${char}' at pos ${i}: '${previous}' -> '${current}' = ${eventType}`);
        }
    }
});
