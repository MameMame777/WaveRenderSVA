"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.WaveformGenerator = void 0;
class WaveformGenerator {
    static generateFromProtocol(protocolName, _params) {
        const template = this.PROTOCOL_TEMPLATES[protocolName];
        if (!template) {
            throw new Error(`Unknown protocol: ${protocolName}`);
        }
        const signals = [];
        // Generate clock signal
        signals.push({
            name: 'clk',
            wave: 'p'.repeat(template.timing.totalCycles)
        });
        // Generate other signals
        template.signals.forEach(signal => {
            if (signal.name === 'clk')
                return;
            const wave = this.generateSignalWave(signal, template.timing);
            const signalEntry = {
                name: signal.name,
                wave: wave
            };
            if (signal.type === 'data' || signal.type === 'address') {
                const dataArray = [];
                for (let i = 0; i < 3; i++) {
                    dataArray.push(signal.type === 'data' ? `D${i}` : `0x${(0x1000 + i * 4).toString(16)}`);
                }
                signalEntry.data = dataArray;
            }
            signals.push(signalEntry);
        });
        return {
            signal: signals,
            config: { hscale: 1, skin: 'default' },
            head: { text: template.name, tock: 0 },
            foot: { text: template.description, tock: template.timing.totalCycles }
        };
    }
    static generateSignalWave(signal, timing) {
        const wave = new Array(timing.totalCycles).fill('.');
        timing.phases.forEach(phase => {
            const signalPattern = phase.signals[signal.name];
            if (signalPattern) {
                for (let i = 0; i < signalPattern.length && i < phase.duration; i++) {
                    const cycleIndex = phase.startCycle - 1 + i;
                    if (cycleIndex < timing.totalCycles) {
                        wave[cycleIndex] = signalPattern[i];
                    }
                }
            }
        });
        return wave.join('');
    }
    static getAvailableProtocols() {
        return Object.keys(this.PROTOCOL_TEMPLATES);
    }
    static getProtocolTemplate(protocolName) {
        return this.PROTOCOL_TEMPLATES[protocolName];
    }
}
exports.WaveformGenerator = WaveformGenerator;
WaveformGenerator.PROTOCOL_TEMPLATES = {
    spi_transaction: {
        name: 'SPI Transaction',
        description: 'Clean SPI transaction protocol',
        signals: [
            { name: 'clk', type: 'clock' },
            { name: 'spi_clk', type: 'clock' },
            { name: 'cs', type: 'control', role: 'handshake' },
            { name: 'mosi', type: 'data', width: 1 },
            { name: 'miso', type: 'data', width: 1 }
        ],
        timing: {
            totalCycles: 23,
            phases: [
                {
                    name: 'idle',
                    startCycle: 1,
                    duration: 3,
                    signals: {
                        'spi_clk': '0..',
                        'cs': '1..',
                        'mosi': '0..',
                        'miso': 'z..'
                    }
                },
                {
                    name: 'active',
                    startCycle: 4,
                    duration: 16,
                    signals: {
                        'spi_clk': '0lhlhlhlhlhlhlhl',
                        'cs': '0...............',
                        'mosi': '0=.....=.....=.',
                        'miso': 'z=.....=.....=.'
                    }
                },
                {
                    name: 'complete',
                    startCycle: 20,
                    duration: 4,
                    signals: {
                        'spi_clk': '0...',
                        'cs': '1...',
                        'mosi': '0...',
                        'miso': 'z...'
                    }
                }
            ]
        },
        parameters: {
            dataWidth: 8
        }
    }
};
//# sourceMappingURL=waveformGenerator.js.map