// Debug test for SVA generator
const fs = require('fs');

// Import compiled SVA generator
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

console.log('Test JSON:', testJson);

const generator = new WaveformToSVAGenerator();
const result = generator.generateSVA(testJson);

console.log('\n=== SVA Generation Result ===');
console.log('Success:', result.success);
console.log('Properties:', result.properties);
console.log('Warnings:', result.warnings);
console.log('Errors:', result.errors);
