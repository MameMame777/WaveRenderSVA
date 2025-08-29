 **SystemVerilog Assertions (SVA)** の典型的な **実例** を、波形イメージや使用シーンごとにまとめます。

---

# SystemVerilog アサーションの実例集

## 1. ハンドシェイク信号の検証

### 要件

`req` が立ったら、**3 サイクル以内に `ack` が 1 になる**。

```systemverilog
property req_ack_handshake;
  @(posedge clk) req |-> ##[1:3] ack;
endproperty

assert property (req_ack_handshake)
  else $error("ACK not asserted within 3 cycles after REQ");
```

* `|->` : **インプリケーション**（もし req が 1 なら → ack が来るべき）
* `##[1:3]` : **1〜3 サイクルの範囲**

---

## 2. リセット動作の確認

### 要件

`reset` がアサートされたら、**次サイクルで `ready=0`、その後 `busy=0` であること**。

```systemverilog
property reset_behavior;
  @(posedge clk) reset |-> ##1 (!ready && !busy);
endproperty

assert property (reset_behavior)
  else $error("Reset did not clear ready/busy correctly");
```

---

## 3. FIFO のオーバーフロー防止

### 要件

`fifo_full` が 1 のときに `write_enable` が 1 になってはいけない。

```systemverilog
property no_fifo_overflow;
  @(posedge clk) not (fifo_full && write_enable);
endproperty

assert property (no_fifo_overflow)
  else $error("FIFO overflow detected!");
```

* `not ( ... )` で **禁止条件** を記述

---

## 4. プロトコル・シーケンスの順序確認

### 要件

`start` → `data_valid` → `done` の順番で信号が出ること。

```systemverilog
property protocol_sequence;
  @(posedge clk)
    start |-> ##[1:5] data_valid ##[1:5] done;
endproperty

assert property (protocol_sequence)
  else $error("Protocol sequence violated (start→data_valid→done)");
```

---

## 5. クロック同期の検証

### 要件

クロックが立ち上がるたびに、`clk_enable` が 1 なら `clk_out` もトグルする。

```systemverilog
property clk_sync;
  @(posedge clk) clk_enable |-> $changed(clk_out);
endproperty

assert property (clk_sync)
  else $error("clk_out did not toggle when clk_enable=1");
```

---

## 6. レイテンシ制約

### 要件

命令 `issue` から **正確に 4 サイクル後に `commit`** が出る。

```systemverilog
property fixed_latency;
  @(posedge clk) issue |-> ##4 commit;
endproperty

assert property (fixed_latency)
  else $error("Commit did not occur exactly 4 cycles after issue");
```

---

## まとめ

* **インプリケーション (|->)** : 条件が成立したらシーケンスが成り立つべき
* **サイクル遅延 (##N, ##\[M\:N])** : 時間的制約を表現
* **禁止条件 (not ...)** : 起こってはいけない事象を監視
* **シーケンスチェーン** : 複数信号の順序関係を検証

---

👉 ご希望なら、次に「WaveDrom の波形 → 自動でこのような SVA に変換する」サンプルを作ってみますか？
