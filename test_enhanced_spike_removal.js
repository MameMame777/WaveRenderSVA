// 強化されたスパイク除去機能のテスト
const { WaveformGenerator } = require('./out/waveformGenerator');
const fs = require('fs');
const path = require('path');

console.log('Testing enhanced spike removal for SPI generation...');

try {
  // 強化されたスパイク除去でSPIを生成
  const spiResult = WaveformGenerator.generateFromProtocol('spi_transaction', {
    dataWidth: 8
  });

  console.log('Generated Enhanced Spike-Free SPI:');
  console.log(JSON.stringify(spiResult, null, 2));
  
  // ファイルに保存
  const outputDir = path.join(__dirname, 'output');
  const jsonFilePath = path.join(outputDir, 'spi_no_spikes_final.json');
  fs.writeFileSync(jsonFilePath, JSON.stringify(spiResult, null, 2));
  console.log(`\n📁 Final spike-free JSON saved to: ${jsonFilePath}`);
  
  // 詳細なスパイク分析
  console.log('\n🔍 Enhanced Spike Analysis:');
  if (spiResult.signal) {
    spiResult.signal.forEach(signal => {
      console.log(`${signal.name}: ${signal.wave}`);
      
      // より詳細なスパイクパターン検出
      const spikePatterns = [
        { pattern: /([01=zlh])\1{2,}/, name: 'Repeated characters' },
        { pattern: /0{2,}/, name: 'Multiple zeros' },
        { pattern: /l{2,}/, name: 'Multiple lows' },
        { pattern: /h{2,}/, name: 'Multiple highs' },
        { pattern: /={2,}/, name: 'Multiple equals' }
      ];
      
      let hasSpikes = false;
      spikePatterns.forEach(({ pattern, name }) => {
        if (pattern.test(signal.wave)) {
          console.log(`  ❌ SPIKE DETECTED: ${name} in ${signal.name}`);
          hasSpikes = true;
        }
      });
      
      if (!hasSpikes) {
        console.log(`  ✅ ${signal.name} is completely spike-free`);
      }
    });
  }

  // 波形品質スコア
  let qualityScore = 100;
  if (spiResult.signal) {
    spiResult.signal.forEach(signal => {
      if (/([01=zlh])\1{2,}/.test(signal.wave)) {
        qualityScore -= 20;
      }
    });
  }
  
  console.log(`\n📊 Wave Quality Score: ${qualityScore}/100`);
  if (qualityScore === 100) {
    console.log('🎉 Perfect spike-free waveform achieved!');
  } else {
    console.log('⚠️  Still has spike artifacts');
  }

} catch (error) {
  console.error('❌ Enhanced generation test failed:', error.message);
}
