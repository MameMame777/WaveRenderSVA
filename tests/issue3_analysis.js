const fs = require('fs');
const { WaveformToSVAGenerator } = require('../out/svaGenerator.js');

console.log('=== Issue #3 Node Position Analysis ===\n');

const issue3JSON = fs.readFileSync('./pat/issue3_node_timing_test.json', 'utf8');
const issue3Data = JSON.parse(issue3JSON);

console.log('Signals and Node Positions:');
issue3Data.signal.forEach(signal => {
  if (signal.node) {
    console.log(`${signal.name}: wave="${signal.wave}", node="${signal.node}"`);
    for (let i = 0; i < signal.node.length; i++) {
      const nodeChar = signal.node[i];
      if (nodeChar !== '.') {
        console.log(`  Node '${nodeChar}' at position ${i}`);
      }
    }
  }
});

console.log('\nEdge Analysis:');
issue3Data.edge.forEach(edge => {
  console.log(`Edge: ${edge}`);
  // Parse edge to find source and target nodes
  const match = edge.match(/([a-zA-Z])([~\-\|>]+)([a-zA-Z])/);
  if (match) {
    const [, source, operator, target] = match;
    console.log(`  ${source} --[${operator}]--> ${target}`);
    
    // Find positions of source and target
    let sourcePos = -1, targetPos = -1;
    issue3Data.signal.forEach(signal => {
      if (signal.node) {
        for (let i = 0; i < signal.node.length; i++) {
          if (signal.node[i] === source) sourcePos = i;
          if (signal.node[i] === target) targetPos = i;
        }
      }
    });
    console.log(`  Position difference: ${target}(${targetPos}) - ${source}(${sourcePos}) = ${targetPos - sourcePos}`);
    console.log(`  Expected operator: ${targetPos - sourcePos === 0 ? '|->' : '|=>'}`);
  }
});

const generator = new WaveformToSVAGenerator();
const result = generator.generateSVA(issue3JSON);

console.log('\nGenerated Properties:');
result.properties.forEach((prop, i) => {
  const isOverlap = prop.includes('|->');
  console.log(`Property ${i+1}: ${isOverlap ? 'OVERLAP (|->)' : 'NON-OVERLAP (|=>)'}`);
  console.log(`  ${prop.split('\n')[1].trim()}`);
});
