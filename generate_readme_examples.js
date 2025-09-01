const { WaveformToSVAGenerator } = require('./out/svaGenerator.js');

// Example 1: 柔軟タイミング (Flexible Timing) - 複数の遅延許容
const flexibleExample = {
  "signal": [
    { "name": "clk", "wave": "p.......", "node": "........" },
    { "name": "req", "wave": "01......", "node": ".a......" },
    { "name": "gnt", "wave": "0..1....", "node": "...b...." },
    { "name": "data", "wave": "x....=..", "node": ".....c.." },
    { "name": "ack", "wave": "0......1", "node": ".......d" }
  ],
  "edge": [
    "a~>b", // req to grant (2 cycle delay, flexible)
    "b~>c", // grant to data (2 cycle delay, flexible) 
    "a~>d"  // req to ack (6 cycle delay, very flexible)
  ]
};

// Example 2: 即時タイミング (Immediate Timing) - 同サイクル関係
const immediateExample = {
  "signal": [
    { "name": "enable", "wave": "01.0....", "node": ".a.b...." },
    { "name": "ready",  "wave": "01.0....", "node": ".c.d...." },
    { "name": "valid",  "wave": "0.10....", "node": "..ef...." },
    { "name": "start",  "wave": "0..1.0..", "node": "...gh..." }
  ],
  "edge": [
    "a->c", // enable to ready (same position, immediate)
    "c->e", // ready to valid (same position, immediate)
    "f->g", // valid fall to start rise (same position)
    "g->h"  // start rise to start fall (same position)
  ]
};

// Example 3: 正確タイミング (Exact Timing) - 固定遅延
const exactExample = {
  "signal": [
    { "name": "trigger", "wave": "01.....", "node": ".a....." },
    { "name": "response", "wave": "0...1..", "node": "....b.." },
    { "name": "timeout", "wave": "0.....1", "node": "......c" }
  ],
  "edge": [
    "a-|>b", // trigger to response (exact 3 cycles)
    "a-|>c"  // trigger to timeout (exact 5 cycles)
  ]
};

const generator = new WaveformToSVAGenerator();

console.log('=== 1. Flexible Timing (柔軟タイミング) ===');
console.log('Input JSON:');
console.log(JSON.stringify(flexibleExample, null, 2));
console.log('\nGenerated SVA:');
const flexResult = generator.generateSVA(JSON.stringify(flexibleExample));
flexResult.properties.forEach((prop, i) => {
  console.log(`\n// Property ${i+1}:`);
  console.log(prop.split('\n').slice(0, 4).join('\n')); // Show first 4 lines
});

console.log('\n=== 2. Immediate Timing (即時タイミング) ===');
console.log('Input JSON:');
console.log(JSON.stringify(immediateExample, null, 2));
console.log('\nGenerated SVA:');
const immResult = generator.generateSVA(JSON.stringify(immediateExample));
immResult.properties.forEach((prop, i) => {
  console.log(`\n// Property ${i+1}:`);
  console.log(prop.split('\n').slice(0, 4).join('\n')); // Show first 4 lines
});

console.log('\n=== 3. Exact Timing (正確タイミング) ===');
console.log('Input JSON:');
console.log(JSON.stringify(exactExample, null, 2));
console.log('\nGenerated SVA:');
const exactResult = generator.generateSVA(JSON.stringify(exactExample));
exactResult.properties.forEach((prop, i) => {
  console.log(`\n// Property ${i+1}:`);
  console.log(prop.split('\n').slice(0, 4).join('\n')); // Show first 4 lines
});

console.log('\n=== Summary ===');
console.log(`Flexible: ${flexResult.properties.length} properties`);
console.log(`Immediate: ${immResult.properties.length} properties`);
console.log(`Exact: ${exactResult.properties.length} properties`);
