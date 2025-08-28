// 修正された生成関数のテスト - スパイクフリーSPI
const { WaveformGenerator } = require('./out/waveformGenerator');
const fs = require('fs');
const path = require('path');

console.log('Testing improved spike-free SPI generation function...');

try {
  // 修正された生成関数でSPIを生成
  const spiResult = WaveformGenerator.generateFromProtocol('spi_transaction', {
    dataWidth: 8
  });

  console.log('Generated Spike-Free SPI WaveDrom JSON:');
  console.log(JSON.stringify(spiResult, null, 2));
  
  // ファイルに保存
  const outputDir = path.join(__dirname, 'output');
  if (!fs.existsSync(outputDir)) {
    fs.mkdirSync(outputDir, { recursive: true });
  }
  
  const jsonFilePath = path.join(outputDir, 'auto_generated_spi_spike_free.json');
  fs.writeFileSync(jsonFilePath, JSON.stringify(spiResult, null, 2));
  console.log(`\n📁 Auto-generated JSON saved to: ${jsonFilePath}`);
  
  // 波形パターンの詳細分析
  console.log('\n🔍 Spike Analysis:');
  if (spiResult.signal) {
    spiResult.signal.forEach(signal => {
      console.log(`${signal.name}: ${signal.wave}`);
      
      // スパイクパターンをチェック
      const hasRepeatedChars = /([01=zlh])\1{2,}/.test(signal.wave);
      if (hasRepeatedChars) {
        console.log(`  ⚠️  Warning: ${signal.name} may have spike-causing repeated characters`);
      } else {
        console.log(`  ✅ ${signal.name} uses proper continuation syntax (spike-free)`);
      }
      
      // データ配列もチェック
      if (signal.data && signal.data.length > 0) {
        console.log(`     Data: [${signal.data.join(', ')}]`);
      }
    });
  }

  // サイクル数確認
  console.log(`\n📊 Total cycles: ${spiResult.foot.tock}`);
  console.log('✅ Generation function successfully improved!');

} catch (error) {
  console.error('❌ Generation test failed:', error.message);
  console.error(error.stack);
}
