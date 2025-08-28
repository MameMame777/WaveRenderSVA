export interface ProtocolSignal {
  name: string;
  type: 'clock' | 'data' | 'control' | 'address';
  width?: number;
  role?: 'handshake' | 'trigger' | 'status';
}

export interface ProtocolPhase {
  name: string;
  startCycle: number;
  duration: number;
  signals: { [signalName: string]: string };
}

export interface ProtocolTiming {
  totalCycles: number;
  phases: ProtocolPhase[];
}

export interface ProtocolParameters {
  dataWidth?: number;
  addressWidth?: number;
  clockFreq?: number;
}

export interface ProtocolTemplate {
  name: string;
  description: string;
  signals: ProtocolSignal[];
  timing: ProtocolTiming;
  parameters: ProtocolParameters;
}

export class WaveformGenerator {
  private static readonly PROTOCOL_TEMPLATES: { [key: string]: ProtocolTemplate } = {
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

  static generateFromProtocol(protocolName: string, params?: Partial<ProtocolParameters>): any {
    const template = this.PROTOCOL_TEMPLATES[protocolName];
    if (!template) {
      throw new Error(`Unknown protocol: ${protocolName}`);
    }

    const signals: any[] = [];

    // Generate clock signal
    signals.push({
      name: 'clk',
      wave: 'p'.repeat(template.timing.totalCycles)
    });

    // Generate other signals
    template.signals.forEach(signal => {
      if (signal.name === 'clk') return;

      const wave = this.generateSignalWave(signal, template.timing);
      const signalEntry: any = {
        name: signal.name,
        wave: wave
      };

      if (signal.type === 'data' || signal.type === 'address') {
        const dataArray: string[] = [];
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

  private static generateSignalWave(signal: ProtocolSignal, timing: ProtocolTiming): string {
    const wave: string[] = new Array(timing.totalCycles).fill('.');

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

  static getAvailableProtocols(): string[] {
    return Object.keys(this.PROTOCOL_TEMPLATES);
  }

  static getProtocolTemplate(protocolName: string): ProtocolTemplate | undefined {
    return this.PROTOCOL_TEMPLATES[protocolName];
  }
}