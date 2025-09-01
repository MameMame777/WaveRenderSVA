const { WaveformToSVAGenerator } = require('./out/svaGenerator.js');
const fs = require('fs');

const testData = fs.readFileSync('test.json', 'utf8');
console.log('Input data:', testData);

// Parse to analyze node positions
const parsedData = JSON.parse(testData);
console.log('\n=== Node Position Analysis ===');
parsedData.signal.forEach(signal => {
  if (signal.node) {
    console.log(`${signal.name}: wave="${signal.wave}", node="${signal.node}"`);
    // Analyze node positions
    for (let i = 0; i < signal.node.length; i++) {
      const nodeChar = signal.node[i];
      if (nodeChar !== '.') {
        console.log(`  Node '${nodeChar}' at position ${i}`);
      }
    }
  }
});

console.log('\n=== Edge Analysis ===');
parsedData.edge.forEach(edge => {
  console.log(`Edge: ${edge}`);
  // Parse edge to find source and target nodes
  const match = edge.match(/([a-zA-Z])([~\-\|>]+)([a-zA-Z])/);
  if (match) {
    const [, source, operator, target] = match;
    console.log(`  ${source} --[${operator}]--> ${target}`);
    
    // Find positions of source and target
    let sourcePos = -1, targetPos = -1;
    parsedData.signal.forEach(signal => {
      if (signal.node) {
        for (let i = 0; i < signal.node.length; i++) {
          if (signal.node[i] === source) sourcePos = i;
          if (signal.node[i] === target) targetPos = i;
        }
      }
    });
    console.log(`  Position difference: ${target}(${targetPos}) - ${source}(${sourcePos}) = ${targetPos - sourcePos}`);
  }
});

const generator = new WaveformToSVAGenerator();
const result = generator.generateSVA(testData);

console.log('\n=== Test Result ===');
console.log('Success:', result.success);
console.log('Properties count:', result.properties ? result.properties.length : 0);

if (result.properties && result.properties.length > 0) {
  console.log('\n=== Generated Properties ===');
  result.properties.forEach((prop, index) => {
    console.log(`\n// Property ${index + 1}:`);
    console.log(prop);
  });
  
  console.log('\n=== Analysis ===');
  console.log('Looking for timing differences and implication operators:');
  
  // Extract key information from generated properties
  result.properties.forEach((prop, index) => {
    console.log(`\nProperty ${index + 1} analysis:`);
    if (prop.includes('|->')) {
      console.log('  - ✅ Uses overlapped implication (|->)');
    }
    if (prop.includes('|=>')) {
      console.log('  - ❌ Uses non-overlapped implication (|=>) - May need fixing for same-position nodes');
    }
    if (prop.includes('##[0:1]')) {
      console.log('  - Has flexible timing constraint ##[0:1]');
    }
  });
}
