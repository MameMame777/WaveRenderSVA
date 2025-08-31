"use strict";
/**
 * Tests for WaveformToSVAGenerator
 * Based on WAVEDROM_SVA_MAPPING.md specification
 */
Object.defineProperty(exports, "__esModule", { value: true });
const svaGenerator_1 = require("../svaGenerator");
describe('WaveformToSVAGenerator', () => {
    let generator;
    beforeEach(() => {
        generator = new svaGenerator_1.WaveformToSVAGenerator();
    });
    describe('基本的なSharp Line変換', () => {
        test('a->c エッジの変換', () => {
            const input = {
                "signal": [
                    { "name": "req", "wave": "01.0", "node": ".a.b" },
                    { "name": "ack", "wave": "0.10", "node": "..c." }
                ],
                "edge": ["a->c"]
            };
            const result = generator.generateSVA(JSON.stringify(input));
            expect(result.success).toBe(true);
            expect(result.properties.length).toBe(1);
            expect(result.properties[0]).toContain('$rose(req) |=> ##1 $rose(ack)');
            expect(result.statistics.sharpLines).toBe(1);
            expect(result.statistics.totalEdges).toBe(1);
        });
        test('同一位置ノードの処理', () => {
            const input = {
                "signal": [
                    { "name": "req", "wave": "01", "node": ".a" },
                    { "name": "ack", "wave": "01", "node": ".b" }
                ],
                "edge": ["a->b"]
            };
            const result = generator.generateSVA(JSON.stringify(input));
            expect(result.success).toBe(true);
            expect(result.properties[0]).toContain('$rose(req) |=> $rose(ack)');
        });
    });
    describe('Splines変換', () => {
        test('a~>b エッジの変換', () => {
            const input = {
                "signal": [
                    { "name": "req", "wave": "01", "node": ".a" },
                    { "name": "ack", "wave": "01", "node": ".b" }
                ],
                "edge": ["a~>b"]
            };
            const result = generator.generateSVA(JSON.stringify(input));
            expect(result.success).toBe(true);
            expect(result.properties[0]).toContain('$rose(req) |-> ##[0:$] $rose(ack)');
            expect(result.statistics.splines).toBe(1);
        });
        test('-~> オペレータの変換', () => {
            const input = {
                "signal": [
                    { "name": "req", "wave": "01", "node": ".a" },
                    { "name": "ack", "wave": "01", "node": ".b" }
                ],
                "edge": ["a-~>b"]
            };
            const result = generator.generateSVA(JSON.stringify(input));
            expect(result.success).toBe(true);
            expect(result.properties[0]).toContain('$rose(req) |=> ##[1:$] $rose(ack)');
        });
    });
    describe('条件付きアサーション', () => {
        test('iff条件の解析', () => {
            const input = {
                "signal": [
                    { "name": "req", "wave": "01", "node": ".a" },
                    { "name": "ack", "wave": "01", "node": ".b" }
                ],
                "edge": ["a->b $iff (enable)$"]
            };
            const result = generator.generateSVA(JSON.stringify(input));
            expect(result.success).toBe(true);
            expect(result.properties[0]).toContain('iff (enable)');
            expect(result.statistics.conditional).toBe(1);
        });
        test('disable_iff条件の解析', () => {
            const input = {
                "signal": [
                    { "name": "req", "wave": "01", "node": ".a" },
                    { "name": "ack", "wave": "01", "node": ".b" }
                ],
                "edge": ["a->b $disable_iff (!rst_n)$"]
            };
            const result = generator.generateSVA(JSON.stringify(input));
            expect(result.success).toBe(true);
            expect(result.properties[0]).toContain('disable iff (!rst_n)');
        });
        test('複合条件の解析', () => {
            const input = {
                "signal": [
                    { "name": "req", "wave": "01", "node": ".a" },
                    { "name": "ack", "wave": "01", "node": ".b" }
                ],
                "edge": ["a->b $iff (enable && ready)$ $disable_iff (!clk_en)$"]
            };
            const result = generator.generateSVA(JSON.stringify(input));
            expect(result.success).toBe(true);
            expect(result.properties[0]).toContain('iff (enable && ready)');
            expect(result.properties[0]).toContain('disable iff (!clk_en)');
        });
    });
    describe('双方向関係', () => {
        test('a<->b エッジの双方向変換', () => {
            const input = {
                "signal": [
                    { "name": "sig_a", "wave": "01", "node": ".a" },
                    { "name": "sig_b", "wave": "01", "node": ".b" }
                ],
                "edge": ["a<->b"]
            };
            const result = generator.generateSVA(JSON.stringify(input));
            expect(result.success).toBe(true);
            expect(result.properties.length).toBeGreaterThan(1); // A->B, B->A
            expect(result.properties.join('')).toContain('$rose(sig_a) |=> $rose(sig_b)');
            expect(result.properties.join('')).toContain('$rose(sig_b) |=> $rose(sig_a)');
            expect(result.statistics.bidirectional).toBe(1);
        });
    });
    describe('エラー処理', () => {
        test('無効ノードのエラー処理', () => {
            const input = {
                "signal": [{ "name": "req", "wave": "01", "node": ".a" }],
                "edge": ["a->x"] // 'x'は存在しない
            };
            const result = generator.generateSVA(JSON.stringify(input));
            expect(result.success).toBe(true);
            expect(result.warnings.length).toBeGreaterThan(0);
            expect(result.warnings.some(w => w.includes('未定義ノード: x'))).toBe(true);
            expect(result.statistics.invalidEdges).toBe(0); // パースは成功、ノードが見つからない
        });
        test('JSON構文エラーの処理', () => {
            const invalidJson = `{
        "signal": [
          {"name": "req", "wave": "01" // 無効なJSON
        ],
        "edge": ["a->b"]
      }`;
            const result = generator.generateSVA(invalidJson);
            expect(result.success).toBe(false);
            expect(result.errors.length).toBeGreaterThan(0);
            expect(result.errors.some(e => e.includes('JSON解析エラー'))).toBe(true);
        });
        test('構文エラー条件の無視', () => {
            const input = {
                "signal": [
                    { "name": "req", "wave": "01", "node": ".a" },
                    { "name": "ack", "wave": "01", "node": ".b" }
                ],
                "edge": ["a->b $iff (invalid_syntax))$"] // 構文エラー
            };
            const result = generator.generateSVA(JSON.stringify(input));
            expect(result.success).toBe(true);
            expect(result.properties[0]).not.toContain('iff (invalid_syntax))'); // 無効な条件は無視
            expect(result.warnings.length).toBeGreaterThan(0);
        });
    });
    describe('イベントタイプ検出', () => {
        test('立ち上がりエッジの検出', () => {
            const input = {
                "signal": [
                    { "name": "clk", "wave": "01010101", "node": ".a......" },
                    { "name": "data", "wave": "0......1", "node": ".......b" }
                ],
                "edge": ["a->b"]
            };
            const result = generator.generateSVA(JSON.stringify(input));
            expect(result.success).toBe(true);
            expect(result.properties[0]).toContain('$rose(clk)');
            expect(result.properties[0]).toContain('$rose(data)');
        });
        test('データ変化の検出', () => {
            const input = {
                "signal": [
                    { "name": "addr", "wave": "x=.=.=.x", "data": ["A1", "A2", "A3"], "node": ".a....." },
                    { "name": "data", "wave": "x.=.=.=", "data": ["D1", "D2", "D3"], "node": "..b...." }
                ],
                "edge": ["a->b"]
            };
            const result = generator.generateSVA(JSON.stringify(input));
            expect(result.success).toBe(true);
            expect(result.properties[0]).toContain('$changed(addr)');
            expect(result.properties[0]).toContain('$changed(data)');
        });
    });
    describe('タイミング計算', () => {
        test('正の時間差の計算', () => {
            const input = {
                "signal": [
                    { "name": "req", "wave": "01.....", "node": ".a....." },
                    { "name": "ack", "wave": "0...1..", "node": "....b.." }
                ],
                "edge": ["a->b"]
            };
            const result = generator.generateSVA(JSON.stringify(input));
            expect(result.success).toBe(true);
            expect(result.properties[0]).toContain('##3'); // 位置4-1=3
        });
        test('逆方向エッジの処理', () => {
            const input = {
                "signal": [
                    { "name": "req", "wave": "0...1..", "node": "....a.." },
                    { "name": "ack", "wave": "01.....", "node": ".b....." }
                ],
                "edge": ["a->b"] // 逆方向
            };
            const result = generator.generateSVA(JSON.stringify(input));
            expect(result.success).toBe(true);
            expect(result.warnings.some(w => w.includes('逆方向エッジ検出'))).toBe(true);
            expect(result.properties[0]).toContain('##3'); // |4-1| = 3
        });
    });
    describe('複雑なサンプル', () => {
        test('仕様書のサンプルJSONの処理', () => {
            const sampleInput = {
                "signal": [
                    { "name": "enable", "wave": "01...........0.", "node": ".c........." },
                    { "name": "Spilne-A", "wave": "01........0....", "node": ".a........j" },
                    { "name": "Spilne-B", "wave": "0.1.......0.1..", "node": "..b.......i" },
                    { "name": "Sharp-A", "wave": "01........0....", "node": ".k........u" },
                    { "name": "Sharp-B", "wave": "0.1.......0.1..", "node": "..l........v" }
                ],
                "edge": [
                    "a~b",
                    "k->l",
                    "c<->a $iff (enable)$"
                ]
            };
            const result = generator.generateSVA(JSON.stringify(sampleInput));
            expect(result.success).toBe(true);
            expect(result.properties.length).toBeGreaterThan(2); // 少なくとも3つのエッジ（双方向は2つ生成）
            expect(result.statistics.splines).toBeGreaterThan(0);
            expect(result.statistics.sharpLines).toBeGreaterThan(0);
            expect(result.statistics.bidirectional).toBeGreaterThan(0);
            expect(result.statistics.conditional).toBeGreaterThan(0);
        });
    });
    describe('統計情報', () => {
        test('統計の正確性', () => {
            const input = {
                "signal": [
                    { "name": "a", "wave": "01", "node": ".a" },
                    { "name": "b", "wave": "01", "node": ".b" },
                    { "name": "c", "wave": "01", "node": ".c" },
                    { "name": "d", "wave": "01", "node": ".d" }
                ],
                "edge": [
                    "a->b",
                    "c~>d",
                    "a<->c",
                    "b->d $iff (en)$" // Conditional
                ]
            };
            const result = generator.generateSVA(JSON.stringify(input));
            expect(result.success).toBe(true);
            expect(result.statistics.totalEdges).toBe(4);
            expect(result.statistics.sharpLines).toBe(2); // a->b, a<->c
            expect(result.statistics.splines).toBe(1); // c~>d
            expect(result.statistics.bidirectional).toBe(1); // a<->c
            expect(result.statistics.conditional).toBe(1); // $iff (en)$
        });
    });
});
//# sourceMappingURL=svaGenerator.test.js.map