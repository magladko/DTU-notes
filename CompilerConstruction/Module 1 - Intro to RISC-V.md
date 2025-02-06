Open Source Instruction Set Architecture (ISA)

**RV32IMF**
- RV32I: base integer instructions and registers (32-bit)
- M extension: integer multiplication and division instructions
- F extension: single-precision (32-bit) floating-point registers and instructions

## RV32I

32 registers x 32 bits

<table class="table" id="table-riscv-base-registers">
<caption><span class="caption-number">Table 2 </span><span class="caption-text">32-bit RISC-V base integer registers.</span><a class="headerlink" href="#table-riscv-base-registers" title="Link to this table">#</a></caption>
<thead>
<tr class="row-odd"><th class="head"><p>Base register name</p></th>
<th class="head"><p>Symbolic name</p></th>
<th class="head"><p>Description</p></th>
<th class="head"><p>Saved by</p></th>
</tr>
</thead>
<tbody>
<tr class="row-even"><td><p><code class="docutils literal notranslate"><span class="pre">x0</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">zero</span></code></p></td>
<td><p>Hard-wired zero</p></td>
<td><p>_</p></td>
</tr>
<tr class="row-odd"><td><p><code class="docutils literal notranslate"><span class="pre">x1</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">ra</span></code></p></td>
<td><p>Return address</p></td>
<td><p>Caller</p></td>
</tr>
<tr class="row-even"><td><p><code class="docutils literal notranslate"><span class="pre">x2</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">sp</span></code></p></td>
<td><p>Stack pointer</p></td>
<td><p>Callee</p></td>
</tr>
<tr class="row-odd"><td><p><code class="docutils literal notranslate"><span class="pre">x3</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">gp</span></code></p></td>
<td><p>Global pointer</p></td>
<td><p>_</p></td>
</tr>
<tr class="row-even"><td><p><code class="docutils literal notranslate"><span class="pre">x4</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">tp</span></code></p></td>
<td><p>Thread pointer</p></td>
<td><p>_</p></td>
</tr>
<tr class="row-odd"><td><p><code class="docutils literal notranslate"><span class="pre">x5</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">t0</span></code></p></td>
<td><p>Temporary / alternate link register</p></td>
<td><p>Caller</p></td>
</tr>
<tr class="row-even"><td><p><code class="docutils literal notranslate"><span class="pre">x6</span></code> – <code class="docutils literal notranslate"><span class="pre">x7</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">t1</span></code> – <code class="docutils literal notranslate"><span class="pre">t2</span></code></p></td>
<td><p>Temporaries</p></td>
<td><p>Caller</p></td>
</tr>
<tr class="row-odd"><td><p><code class="docutils literal notranslate"><span class="pre">x8</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">s0</span></code> / <code class="docutils literal notranslate"><span class="pre">fp</span></code></p></td>
<td><p>Saved register / frame pointer</p></td>
<td><p>Callee</p></td>
</tr>
<tr class="row-even"><td><p><code class="docutils literal notranslate"><span class="pre">x9</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">s1</span></code></p></td>
<td><p>Saved register</p></td>
<td><p>Callee</p></td>
</tr>
<tr class="row-odd"><td><p><code class="docutils literal notranslate"><span class="pre">x10</span></code> – <code class="docutils literal notranslate"><span class="pre">x11</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">a0</span></code> – <code class="docutils literal notranslate"><span class="pre">a1</span></code></p></td>
<td><p>Function arguments / return values</p></td>
<td><p>Caller</p></td>
</tr>
<tr class="row-even"><td><p><code class="docutils literal notranslate"><span class="pre">x12</span></code> – <code class="docutils literal notranslate"><span class="pre">x17</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">a2</span></code> – <code class="docutils literal notranslate"><span class="pre">a7</span></code></p></td>
<td><p>Function arguments</p></td>
<td><p>Caller</p></td>
</tr>
<tr class="row-odd"><td><p><code class="docutils literal notranslate"><span class="pre">x18</span></code> – <code class="docutils literal notranslate"><span class="pre">x27</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">s2</span></code> – <code class="docutils literal notranslate"><span class="pre">s11</span></code></p></td>
<td><p>Saved registers</p></td>
<td><p>Callee</p></td>
</tr>
<tr class="row-even"><td><p><code class="docutils literal notranslate"><span class="pre">x28</span></code> – <code class="docutils literal notranslate"><span class="pre">x31</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">t3</span></code> – <code class="docutils literal notranslate"><span class="pre">t6</span></code></p></td>
<td><p>Temporaries</p></td>
<td><p>Caller</p></td>
</tr>
</tbody>
</table>

![[RV32I_instruction_set_table.png]]

## F extension

32 single-precision floating-point registers x 32 bits

<table class="table" id="table-riscv-fp-registers">
<caption><span class="caption-number">Table 3 </span><span class="caption-text">RISC-V single-precision floating-point registers.</span><a class="headerlink" href="#table-riscv-fp-registers" title="Link to this table">#</a></caption>
<thead>
<tr class="row-odd"><th class="head"><p>Floating-point register name</p></th>
<th class="head"><p>Symbolic name</p></th>
<th class="head"><p>Description</p></th>
<th class="head"><p>Saved by</p></th>
</tr>
</thead>
<tbody>
<tr class="row-even"><td><p><code class="docutils literal notranslate"><span class="pre">f0</span></code> – <code class="docutils literal notranslate"><span class="pre">f7</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">ft0</span></code> – <code class="docutils literal notranslate"><span class="pre">ft7</span></code></p></td>
<td><p>Floating-point temporaries</p></td>
<td><p>Caller</p></td>
</tr>
<tr class="row-odd"><td><p><code class="docutils literal notranslate"><span class="pre">f8</span></code> – <code class="docutils literal notranslate"><span class="pre">f9</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">fs0</span></code> – <code class="docutils literal notranslate"><span class="pre">f1</span></code></p></td>
<td><p>Floating-point saved registers</p></td>
<td><p>Callee</p></td>
</tr>
<tr class="row-even"><td><p><code class="docutils literal notranslate"><span class="pre">f10</span></code> – <code class="docutils literal notranslate"><span class="pre">f11</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">fa0</span></code> – <code class="docutils literal notranslate"><span class="pre">fa1</span></code></p></td>
<td><p>Floating-point arguments/return values</p></td>
<td><p>Caller</p></td>
</tr>
<tr class="row-odd"><td><p><code class="docutils literal notranslate"><span class="pre">f12</span></code> – <code class="docutils literal notranslate"><span class="pre">f17</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">fa2</span></code> – <code class="docutils literal notranslate"><span class="pre">fa7</span></code></p></td>
<td><p>Floating-point arguments</p></td>
<td><p>Caller</p></td>
</tr>
<tr class="row-even"><td><p><code class="docutils literal notranslate"><span class="pre">f18</span></code> – <code class="docutils literal notranslate"><span class="pre">f27</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">fs2</span></code> – <code class="docutils literal notranslate"><span class="pre">fs11</span></code></p></td>
<td><p>Floating-point saved registers</p></td>
<td><p>Callee</p></td>
</tr>
<tr class="row-odd"><td><p><code class="docutils literal notranslate"><span class="pre">f28</span></code> – <code class="docutils literal notranslate"><span class="pre">f31</span></code></p></td>
<td><p><code class="docutils literal notranslate"><span class="pre">ft8</span></code> – <code class="docutils literal notranslate"><span class="pre">ft11</span></code></p></td>
<td><p>Floating-point temporaries</p></td>
<td><p>Caller</p></td>
</tr>
</tbody>
</table>

![[riscv_fp_register_table.png]]

## RISC-V instructions

<table class="longtable table">
<colgroup>
<col style="width: 36.8%">
<col style="width: 26.3%">
<col style="width: 36.8%">
</colgroup>
<thead>
<tr class="row-odd"><th class="head"><p>Syntax</p></th>
<th class="head"><p>Name</p></th>
<th class="head"><p>Description</p></th>
</tr>
</thead>
<tbody>
<tr class="row-even"><td><p><code class="docutils literal notranslate"><span class="pre">li</span> <span class="pre">rd,</span> <span class="pre">val</span></code></p></td>
<td><p>Load immediate</p></td>
<td><p>Load into register <code class="docutils literal notranslate"><span class="pre">rd</span></code> the 32-bit value <code class="docutils literal notranslate"><span class="pre">val</span></code>.  (Pseudo instruction)</p></td>
</tr>
<tr class="row-odd"><td><p><code class="docutils literal notranslate"><span class="pre">lw</span> <span class="pre">rd,</span> <span class="pre">label</span></code></p></td>
<td><p>Load word</p></td>
<td><p>Load into register <code class="docutils literal notranslate"><span class="pre">rd</span></code> the word stored at memory address <code class="docutils literal notranslate"><span class="pre">label</span></code>.
(Pseudo instruction)</p></td>
</tr>
<tr class="row-even"><td><p><code class="docutils literal notranslate"><span class="pre">la</span> <span class="pre">rd,</span> <span class="pre">label</span></code></p></td>
<td><p>Load absolute</p></td>
<td><p>Load into register <code class="docutils literal notranslate"><span class="pre">rd</span></code> the memory address <code class="docutils literal notranslate"><span class="pre">label</span></code>.  (Pseudo instruction)</p></td>
</tr>
<tr class="row-odd"><td><p><code class="docutils literal notranslate"><span class="pre">mv</span> <span class="pre">rd,</span> <span class="pre">rs</span></code></p></td>
<td><p>Move</p></td>
<td><p>Move (i.e. copy) the content of register <code class="docutils literal notranslate"><span class="pre">rs</span></code> into register <code class="docutils literal notranslate"><span class="pre">rd</span></code>.</p></td>
</tr>
<tr class="row-even"><td><p><code class="docutils literal notranslate"><span class="pre">sw</span> <span class="pre">rs2,</span> <span class="pre">offset(rs1)</span></code></p></td>
<td><p>Store word</p></td>
<td><p>Store the 32-bit value contained in the register <code class="docutils literal notranslate"><span class="pre">rs2</span></code> into memory.  The
destination memory address is computed adding the value <code class="docutils literal notranslate"><span class="pre">offset</span></code> to the
content of register <code class="docutils literal notranslate"><span class="pre">rs1</span></code>.</p></td>
</tr>
</tbody>
</table>
