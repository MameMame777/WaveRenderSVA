const fs = require('fs');
const { WaveformToSVAGenerator } = require('../out/svaGenerator.js');

console.log('=== Regression Test: Timing-Aware Implication Operators ===\n');

// Test 1: Issue #3 dedicated test (same-position nodes)
console.log('Test 1: Issue #3 Node Timing Test');
const issue3JSON = fs.readFileSync('./pat/issue3_node_timing_test.json', 'utf8');
const generator = new WaveformToSVAGenerator();
const issue3Result = generator.generateSVA(issue3JSON);

console.log('Properties generated:', issue3Result.properties.length);
let overlapCount = 0, nonOverlapCount = 0;
issue3Result.properties.forEach((prop, i) => {
  if (prop.includes('|->')) overlapCount++;
  if (prop.includes('|=>')) nonOverlapCount++;
  console.log(`Property ${i+1}: ${prop.includes('|->') ? 'OVERLAP (|->)' : 'NON-OVERLAP (|=>)'}`);
});

console.log(`\nSummary: ${overlapCount} overlapped, ${nonOverlapCount} non-overlapped\n`);

// Test 2: Comprehensive test
console.log('Test 2: Comprehensive Test (all operators)');
const compJSON = fs.readFileSync('./pat/comprehensive_test.json', 'utf8');
const compResult = generator.generateSVA(compJSON);

let comp_overlap = 0, comp_nonOverlap = 0;
compResult.properties.forEach(prop => {
  if (prop.includes('|->')) comp_overlap++;
  if (prop.includes('|=>')) comp_nonOverlap++;
});

console.log(`Comprehensive: ${comp_overlap} overlapped, ${comp_nonOverlap} non-overlapped`);
console.log(`Total properties: ${compResult.properties.length}`);

// Test 3: Basic same-position test
console.log('\nTest 3: Basic Same-Position Test');
const basicTest = {
  'signal': [
    { 'name': 'sig1', 'wave': '01.0', 'node': '.a.b' },
    { 'name': 'sig2', 'wave': '0.10', 'node': '.c.d' }
  ],
  'edge': ['a->c', 'b->d']  // Both should be same-position
};

const basicResult = generator.generateSVA(JSON.stringify(basicTest));
console.log('Basic test properties:', basicResult.properties.length);
basicResult.properties.forEach((prop, i) => {
  console.log(`Basic ${i+1}: ${prop.includes('|->') ? 'OVERLAP ✅' : 'NON-OVERLAP ❌'}`);
});

// Test 4: Mixed timing test
console.log('\nTest 4: Mixed Timing Test');
const mixedTest = {
  'signal': [
    { 'name': 'clk', 'wave': 'p......', 'node': '.......' },
    { 'name': 'req', 'wave': '01..0..', 'node': '.a..b..' },
    { 'name': 'ack', 'wave': '0.1.0..', 'node': '..c.d..' },
    { 'name': 'data', 'wave': 'x.==.x.', 'node': '..e.f..' }
  ],
  'edge': [
    'a~>c',   // Different position (1->2): should use |=>
    'c->e',   // Same position (2->2): should use |->
    'b-|>d'   // Same position (4->4): should use |->
  ]
};

const mixedResult = generator.generateSVA(JSON.stringify(mixedTest));
console.log('Mixed test properties:', mixedResult.properties.length);
mixedResult.properties.forEach((prop, i) => {
  const edge = mixedTest.edge[i];
  const isOverlap = prop.includes('|->');
  const isCorrect = (edge === 'a~>c' && !isOverlap) || 
                   ((edge === 'c->e' || edge === 'b-|>d') && isOverlap);
  console.log(`${edge}: ${isOverlap ? 'OVERLAP (|->)' : 'NON-OVERLAP (|=>)'} ${isCorrect ? '✅' : '❌'}`);
});

// Test 5: Check for any regression in error/warning generation
console.log('\nTest 5: Error/Warning Regression Check');
console.log(`Issue3 - Errors: ${issue3Result.errors.length}, Warnings: ${issue3Result.warnings.length}`);
console.log(`Comprehensive - Errors: ${compResult.errors.length}, Warnings: ${compResult.warnings.length}`);
console.log(`Basic - Errors: ${basicResult.errors.length}, Warnings: ${basicResult.warnings.length}`);
console.log(`Mixed - Errors: ${mixedResult.errors.length}, Warnings: ${mixedResult.warnings.length}`);

console.log('\n=== Regression Test Complete ===');
