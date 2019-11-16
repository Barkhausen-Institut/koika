Require Import Koika.Frontend.
Require Import Coq.Lists.List.

Require Import Koika.Std.
Require Import RV.RVEncoding.
Require Import RV.Scoreboard.


Section RV32IHelpers.
  Context {reg_t: Type}.
  Import ListNotations.
  Definition imm_type :=
    {| enum_name := "immType";
       enum_bitsize := 3;
       enum_members := vect_of_list ["ImmI"; "ImmS"; "ImmB"; "ImmU"; "ImmJ"];
       enum_bitpatterns := vect_of_list [Bits.of_nat 3 0; Bits.of_nat 3 1; Bits.of_nat 3 2; Bits.of_nat 3 3; Bits.of_nat 3 4]
    |}.

  Definition decoded_sig :=
    {| struct_name := "decodedInst";
       struct_fields := ("valid_rs1", bits_t 1)
                          :: ("valid_rs2"     , bits_t 1)
                          :: ("valid_rd"      , bits_t 1)
                          :: ("legal"         , bits_t 1)
                          :: ("inst"          , bits_t 32)
                          :: ("immediateType" , maybe (enum_t imm_type))
                          :: nil |}.

  Definition inst_field :=
    {| struct_name := "instFields";
       struct_fields := ("opcode", bits_t 7)
                          :: ("funct3" , bits_t 3)
                          :: ("funct7" , bits_t 7)
                          :: ("funct5" , bits_t 5)
                          :: ("funct2" , bits_t 2)
                          :: ("rd"     , bits_t 5)
                          :: ("rs1"    , bits_t 5)
                          :: ("rs2"    , bits_t 5)
                          :: ("rs3"    , bits_t 5)
                          :: ("immI"   , bits_t 32)
                          :: ("immS"   , bits_t 32)
                          :: ("immB"   , bits_t 32)
                          :: ("immU"   , bits_t 32)
                          :: ("immJ"   , bits_t 32)
                          :: ("csr"    , bits_t 12)
                          :: nil
    |}.


  Definition getFields : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun (inst : bits_t 32) : struct_t inst_field =>
          let res := struct inst_field
                            {|
                              opcode := inst[|5`d0| :+ 7];
                              funct3 := inst[|5`d12| :+ 3];
                              funct7 := inst[|5`d25| :+ 7];
                              funct5 := inst[|5`d27| :+ 5];
                              funct2 := inst[|5`d25| :+ 2];
                              rd     := inst[|5`d7| :+ 5];
                              rs1    := inst[|5`d15| :+ 5];
                              rs2    := inst[|5`d20| :+ 5];
                              rs3    := inst[|5`d27| :+ 5];
                              immI   := {signExtend 12 20}(inst[|5`d20| :+ 12]);
                              immS   := {signExtend 12 20}(inst[|5`d25|:+ 7] ++ inst[|5`d7| :+ 5]);
                              immB   := {signExtend 13 19}
                                            (inst[|5`d31|]
                                                 ++ inst[|5`d7|]
                                                 ++ inst[|5`d25| :+ 6]
                                                 ++ inst[|5`d8| :+ 4]
                                                 ++ |1`d0|);
                              immU   := (inst[|5`d12| :+ 20]
                                             ++ |12`d0|);
                              immJ   := {signExtend 21 11}(inst[|5`d31|]
                                                               ++ inst[|5`d12| :+ 8]
                                                               ++ inst[|5`d20|]
                                                               ++ inst[|5`d21|:+10]
                                                               ++ |1`d0|);
                              csr    := (inst[|5`d20| :+ 12]) |} in
          res
        }}.


  Definition isLegalInstruction : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun (inst : bits_t 32) : bits_t 1 =>
          let fields := getFields (inst) in
          match get(fields, opcode) with
          | #opcode_LOAD =>
            match get(fields, funct3) with
            | #funct3_LB  => Ob~1
            | #funct3_LH  => Ob~1
            | #funct3_LW  => Ob~1
            | #funct3_LBU => Ob~1
            | #funct3_LHU => Ob~1
            return default: Ob~0
            end
          | #opcode_OP_IMM =>
            match get(fields,funct3) with
            | #funct3_ADD  => Ob~1 (* SUB is the same funct3*)
            | #funct3_SLT  => Ob~1
            | #funct3_SLTU => Ob~1
            | #funct3_XOR  => Ob~1
            | #funct3_OR   => Ob~1
            | #funct3_AND  => Ob~1
            | #funct3_SLL  =>
              (get(fields,funct7)[|3`d1| :+ 6] == Ob~0~0~0~0~0~0)
                && (get(fields,funct7)[|3`d0|] == Ob~0)
            | #funct3_SRL  =>
              ((get(fields,funct7)[|3`d1| :+ 6] == Ob~0~0~0~0~0~0)
               || (get(fields,funct7)[|3`d1| :+ 6] == Ob~0~1~0~0~0~0))
                && get(fields,funct7)[|3`d0|] == Ob~0 (* All the funct3_SR* are the same *)
            return default: Ob~0
            end
          | #opcode_AUIPC => Ob~1
          | #opcode_STORE =>
            match get(fields, funct3) with
            | #funct3_SB => Ob~1
            | #funct3_SH => Ob~1
            | #funct3_SW => Ob~1
            return default: Ob~0
            end
          | #opcode_OP =>
            match get(fields,funct3) with
            | #funct3_ADD  => (get(fields,funct7) == Ob~0~0~0~0~0~0~0) || get(fields,funct7) == Ob~0~1~0~0~0~0~0
            | #funct3_SRL  => (get(fields,funct7) == Ob~0~0~0~0~0~0~0) || get(fields,funct7) == Ob~0~1~0~0~0~0~0
            | #funct3_SLL  => get(fields,funct7) == Ob~0~0~0~0~0~0~0
            | #funct3_SLT  => get(fields,funct7) == Ob~0~0~0~0~0~0~0
            | #funct3_SLTU => get(fields,funct7) == Ob~0~0~0~0~0~0~0
            | #funct3_XOR  => get(fields,funct7) == Ob~0~0~0~0~0~0~0
            | #funct3_OR   => get(fields,funct7) == Ob~0~0~0~0~0~0~0
            | #funct3_AND  => get(fields,funct7) == Ob~0~0~0~0~0~0~0
            return default: Ob~0
            end
          | #opcode_LUI    => Ob~1
          | #opcode_BRANCH =>
            match get(fields,funct3) with
            | #funct3_BEQ  => Ob~1
            | #funct3_BNE  => Ob~1
            | #funct3_BLT  => Ob~1
            | #funct3_BGE  => Ob~1
            | #funct3_BLTU => Ob~1
            | #funct3_BGEU => Ob~1
            return default: Ob~0
            end
          | #opcode_JALR   => get(fields,funct3) == Ob~0~0~0
          | #opcode_JAL    => Ob~1
          | #opcode_SYSTEM =>
            match get(fields, funct3) with
            | #funct3_PRIV =>
              (get(fields, rd) == Ob~0~0~0~0~0)
                && (match (get(fields, funct7) ++ get(fields, rs2)) with
                    | Ob~0~0~0~0~0~0~0~0~0~0~0~0 => (get(fields, rs1) == Ob~0~0~0~0~0)        (* // ECALL *)
                    | Ob~0~0~0~0~0~0~0~0~0~0~0~1 => (get(fields, rs1) == Ob~0~0~0~0~0)        (* // EBREAK *)
                    | Ob~0~0~1~1~0~0~0~0~0~0~1~0 => (get(fields, rs1) == Ob~0~0~0~0~0)        (* // MRET *)
                    | Ob~0~0~0~1~0~0~0~0~0~1~0~1 => (get(fields, rs1) == Ob~0~0~0~0~0)        (* // WFI *)
                    return default: Ob~0
                    end)
            return default: Ob~0
            end
          return default: Ob~0
          end
    }}.


  Definition getImmediateType : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun (inst : bits_t 32) : maybe (enum_t imm_type) =>
          match (inst[|5`d2|:+5]) with
          | #opcode_LOAD[|3`d2|:+5]      => {valid (enum_t imm_type)}(enum imm_type {| ImmI |})
          | #opcode_OP_IMM[|3`d2|:+5]    => {valid (enum_t imm_type)}(enum imm_type {| ImmI |})
          | #opcode_JALR[|3`d2|:+5]      => {valid (enum_t imm_type)}(enum imm_type {| ImmI |})
          | #opcode_AUIPC[|3`d2|:+5]     => {valid (enum_t imm_type)}(enum imm_type {| ImmU |})
          | #opcode_LUI[|3`d2|:+5]       => {valid (enum_t imm_type)}(enum imm_type {| ImmU |})
          | #opcode_STORE[|3`d2|:+5]     => {valid (enum_t imm_type)}(enum imm_type {| ImmS |})
          | #opcode_BRANCH[|3`d2|:+5]    => {valid (enum_t imm_type)}(enum imm_type {| ImmB |})
          | #opcode_JAL[|3`d2|:+5]       => {valid (enum_t imm_type)}(enum imm_type {| ImmJ |})
          return default: {invalid (enum_t imm_type)}()
          end
    }}.

  Definition usesRS1 : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun (inst : bits_t 32) : bits_t 1 =>
          match (inst[Ob~0~0~0~1~0 :+ 5]) with
          | Ob~1~1~0~0~0 => Ob~1 (* // bge, bne, bltu, blt, bgeu, beq *)
          | Ob~0~0~0~0~0 => Ob~1 (* // lh, ld, lw, lwu, lbu, lhu, lb *)
          | Ob~0~1~0~0~0 => Ob~1 (* // sh, sb, sw, sd *)
          | Ob~0~1~1~0~0 => Ob~1 (* // sll, mulh, sltu, mulhu, slt, mulhsu, or, rem, xor, div, and, remu, srl, divu, sra, add, mul, sub *)
          | Ob~1~1~0~0~1 => Ob~1 (* // jalr *)
          | Ob~0~0~1~0~0 => Ob~1 (* // srli, srli, srai, srai, slli, slli, ori, sltiu, andi, slti, addi, xori *)
          return default: Ob~0
          end
    }}.


  Definition usesRS2 : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun (inst : bits_t 32) : bits_t 1 =>
            match (inst[Ob~0~0~0~1~0 :+ 5]) with
            | Ob~1~1~0~0~0 => Ob~1 (* // bge, bne, bltu, blt, bgeu, beq *)
            | Ob~0~1~0~0~0 => Ob~1 (* // sh, sb, sw, sd *)
            | Ob~0~1~1~0~0 => Ob~1 (* // sll, mulh, sltu, mulhu, slt, mulhsu, or, rem, xor, div, and, remu, srl, divu, sra, add, mul, sub *)
            return default: Ob~0
            end
    }}.


  Definition usesRD : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun (inst : bits_t 32) : bits_t 1 =>
          match (inst[Ob~0~0~0~1~0 :+ 5]) with
          | Ob~0~1~1~0~1 => Ob~1 (* // lui*)
          | Ob~1~1~0~1~1 => Ob~1 (* // jal*)
          | Ob~0~0~0~0~0 => Ob~1 (* // lh, ld, lw, lwu, lbu, lhu, lb*)
          | Ob~0~1~1~0~0 => Ob~1 (* // sll, mulh, sltu, mulhu, slt, mulhsu, or, rem, xor, div, and, remu, srl, divu, sra, add, mul, sub*)
          | Ob~1~1~0~0~1 => Ob~1 (* // jalr*)
          | Ob~0~0~1~0~0 => Ob~1 (* // srli, srli, srai, srai, slli, slli, ori, sltiu, andi, slti, addi, xori*)
          | Ob~0~0~1~0~1 => Ob~1 (* // auipc*)
          return default: Ob~0
          end
    }}.

  Definition decode_fun : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun (arg_inst : bits_t 32) : struct_t decoded_sig =>
           struct decoded_sig {|
                    valid_rs1     := usesRS1 (arg_inst);
                    valid_rs2     := usesRS2 (arg_inst);
                    valid_rd      := usesRD (arg_inst);
                    legal         := isLegalInstruction (arg_inst);
                    inst          := arg_inst;
                    immediateType := getImmediateType(arg_inst)
                  |}
    }}.

  Definition getImmediate : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun (dInst: struct_t decoded_sig) : bits_t 32 =>
          let imm_type_v := get(dInst, immediateType) in
          if (get(imm_type_v, valid) == Ob~1) then
            let fields := getFields (get(dInst,inst)) in
            match (get(imm_type_v, data)) with
            | (enum imm_type {| ImmI |}) => get(fields, immI)
            | (enum imm_type {| ImmS |}) => get(fields, immS)
            | (enum imm_type {| ImmB |}) => get(fields, immB)
            | (enum imm_type {| ImmU |}) => get(fields, immU)
            | (enum imm_type {| ImmJ |}) => get(fields, immJ)
            return default: |32`d0|
            end
          else
            |32`d0|
    }}.

  Definition alu32 : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun (funct3  : bits_t 3)
         (inst_30 : bits_t 1)
         (a       : bits_t 32)
         (b       : bits_t 32)
         : bits_t 32 =>
         let shamt := b[Ob~0~0~0~0~0 :+ 5] in
         match funct3 with
         | #funct3_ADD  => if (inst_30 == Ob~1) then a - b else a + b
         | #funct3_SLL  => a << shamt
         | #funct3_SLT  => zeroExtend(a <s b, 32)
         | #funct3_SLTU => zeroExtend(a < b, 32)
         | #funct3_XOR  => a ^ b
         | #funct3_SRL  => if (inst_30 == Ob~1) then a >>> shamt else a >> shamt
         | #funct3_OR   => a || b
         | #funct3_AND  => a && b
         return default: #(Bits.of_nat 32 0)
         end
    }}.


  Definition execALU32 : UInternalFunction reg_t empty_ext_fn_t :=

    {{
        fun (inst    : bits_t 32)
          (rs1_val : bits_t 32)
          (rs2_val : bits_t 32)
          (imm_val : bits_t 32)
          (pc      : bits_t 32)
          : bits_t 32 =>
          let isLUI := (inst[|5`d2|] == Ob~1) && (inst[|5`d5|] == Ob~1) in
          let isAUIPC := (inst[|5`d2|] == Ob~1) && (inst[|5`d5|] == Ob~0) in
          let isIMM := (inst[|5`d5|] == Ob~0) in
          let rd_val := |32`d0| in
          (if (isLUI) then
             set rd_val := imm_val
           else if (isAUIPC) then
                  set rd_val := (pc + imm_val)
                else
                  let alu_src1 := rs1_val in
                  let alu_src2 := if isIMM then imm_val else rs2_val in
                  let funct3 := get(getFields(inst), funct3) in
                  let inst_30 := inst[|5`d30|] in
                  if ((funct3 == #funct3_ADD) && isIMM) then
                     (* // this is a special caes for addi *)
                     set inst_30 := Ob~0
                  else pass;
                  set rd_val := alu32(funct3, inst_30, alu_src1, alu_src2));
        rd_val
    }}.

  Definition control_result :=
    {| struct_name := "control_result";
       struct_fields := ("nextPC", bits_t 32)
                          :: ("taken" , bits_t 1)
                          :: nil |}.

  Definition execControl32 : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun (inst    : bits_t 32)
          (rs1_val : bits_t 32)
          (rs2_val : bits_t 32)
          (imm_val : bits_t 32)
          (pc      : bits_t 32)
          : struct_t control_result =>
          let isControl := inst[|5`d4| :+ 3] == Ob~1~1~0 in
          let isJAL     := (inst[|5`d2|] == Ob~1) && (inst[|5`d3|] == Ob~1) in
          let isJALR    := (inst[|5`d2|] == Ob~1) && (inst[|5`d3|] == Ob~0) in
          let incPC     := pc + |32`d4| in
          let funct3    := get(getFields(inst), funct3) in
          let taken     := Ob~1 in  (* // for JAL and JALR *)
          let nextPC    := incPC in
          if (!isControl) then
             set taken  := Ob~0;
             set nextPC := incPC
          else
            if (isJAL) then
              set taken  := Ob~1;
              set nextPC := (pc + imm_val)
            else
              if (isJALR) then
                set taken  := Ob~1;
                set nextPC := ((rs1_val + imm_val) && !|32`d1|)
              else
                ((set taken := match (funct3) with
                             | #funct3_BEQ  => (rs1_val == rs2_val)
                             | #funct3_BNE  => !(rs1_val == rs2_val)
                             | #funct3_BLT  => rs1_val <s rs2_val
                             | #funct3_BGE  => !(rs1_val <s rs2_val)
                             | #funct3_BLTU => (rs1_val < rs2_val)
                             | #funct3_BGEU => !(rs1_val < rs2_val)
                             return default: Ob~0
                             end);
                 if (taken) then
                   set nextPC := (pc + imm_val)
                 else
                   set nextPC := incPC);
        struct control_result {| taken  := taken;
                                 nextPC := nextPC |}
    }}.
End RV32IHelpers.


Module  RV32ICore.
  Import ListNotations.

  Definition mem_req :=
    {| struct_name := "mem_req";
       struct_fields := [("byte_en" , bits_t 4);
                         ("addr"     , bits_t 32);
                         ("data"     , bits_t 32)] |}.
  Definition mem_resp :=
    {| struct_name := "mem_resp";
       struct_fields := [("byte_en", bits_t 4); ("addr", bits_t 32); ("data", bits_t 32)] |}.

  Definition fetch_bookkeeping :=
    {| struct_name := "fetch_bookkeeping";
       struct_fields := [("pc"    , bits_t 32);
                         ("ppc"   , bits_t 32);
                         ("epoch" , bits_t 1)] |}.

  Definition decode_bookkeeping :=
    {| struct_name := "decode_bookkeeping";
       struct_fields := [("pc"    , bits_t 32);
                         ("ppc"   , bits_t 32);
                         ("epoch" , bits_t 1);
                         ("dInst" , struct_t decoded_sig);
                         ("rval1" , bits_t 32);
                         ("rval2" , bits_t 32)] |}.

  Definition execute_bookkeeping :=
    {| struct_name := "execute_bookkeeping";
       struct_fields := [("isUnsigned" , bits_t 1);
                         ("size", bits_t 2);
                         ("offset", bits_t 2);
                         ("newrd" , bits_t 32);
                         ("dInst"    , struct_t decoded_sig)]|}.


  (* Specialize interfaces *)
  Module FifoMemReq <: Fifo.
    Definition T:= struct_t mem_req.
  End FifoMemReq.
  Module MemReq := Fifo1 FifoMemReq.

  Module FifoMemResp <: Fifo.
    Definition T:= struct_t mem_resp.
  End FifoMemResp.
  Module MemResp := Fifo1 FifoMemResp.

  Module FifoFetch <: Fifo.
    Definition T:= struct_t fetch_bookkeeping.
  End FifoFetch.
  Module fromFetch := Fifo1 FifoFetch.

  Module FifoDecode <: Fifo.
    Definition T:= struct_t decode_bookkeeping.
  End FifoDecode.
  Module fromDecode := Fifo1 FifoDecode.

  Module FifoExecute <: Fifo.
    Definition T:= struct_t execute_bookkeeping.
  End FifoExecute.
  Module fromExecute := Fifo1 FifoExecute.

  Module Rf_32 <: RfPow2_sig.
    Definition idx_sz := log2 32.
    Definition T := bits_t 32.
    Definition init := Bits.zeroes 32.
  End Rf_32.
  Module Rf := RfPow2 Rf_32.

  Module Scoreboard_32reg <: Scoreboard_sig.
    Definition lastIdx := 31.
    Definition maxScore := 3.
  End Scoreboard_32reg.
  Module Scoreboard := Scoreboard Scoreboard_32reg.


  (* Declare state *)
  Inductive reg_t :=
  | toIMem (state: MemReq.reg_t)
  | fromIMem (state: MemResp.reg_t)
  | toDMem (state: MemReq.reg_t)
  | fromDMem (state: MemResp.reg_t)
  | f2d (state: fromFetch.reg_t)
  | d2e (state: fromDecode.reg_t)
  | e2w (state: fromExecute.reg_t)
  | rf (state: Rf.reg_t)
  | scoreboard (state: Scoreboard.reg_t)
  | pc
  | epoch.

  (* Boiler-plate typing state *)
  Definition R idx :=
    match idx with
    | toIMem r => MemReq.R r
    | fromIMem r => MemResp.R r
    | toDMem r => MemReq.R r
    | fromDMem r => MemResp.R r
    | f2d r => fromFetch.R r
    | d2e r => fromDecode.R r
    | e2w r => fromExecute.R r
    | rf r => Rf.R r
    | scoreboard r => Scoreboard.R r
    | pc => bits_t 32
    | epoch => bits_t 1
    end.

  (* Boiler-plate init value state *)
  Definition r idx : R idx :=
    match idx with
    | rf s => Rf.r s
    | toIMem s => MemReq.r s
    | fromIMem s => MemResp.r s
    | toDMem s => MemReq.r s
    | fromDMem s => MemResp.r s
    | f2d s => fromFetch.r s
    | d2e s => fromDecode.r s
    | e2w s => fromExecute.r s
    | scoreboard s => Scoreboard.r s
    | pc => Ob~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | epoch => Bits.zero
    end.

  Definition fetch : uaction reg_t empty_ext_fn_t :=
    {{
        let pc := read0(pc) in
        let req := struct mem_req {|
                              byte_en := |4`d0|; (* Load *)
                              addr := pc;
                              data := |32`d0| |} in
        let fetch_bookkeeping := struct fetch_bookkeeping {|
                                          pc := pc;
                                          ppc := pc + |32`d4|;
                                          epoch := read0(epoch)
                                        |} in
        toIMem.(MemReq.enq)(req);
        write0(pc, pc + |32`d4|);
        f2d.(fromFetch.enq)(fetch_bookkeeping)
    }}.

  Definition tc_fetch :=
    tc_action R empty_Sigma fetch .

  (* This rule is interesting because maybe we want to write it *)
  (* differently than Bluespec if we care about simulation *)
  (* performance. Moreover, we could read unconditionaly to avoid potential *)
  (* muxing on the input, TODO check if it changes anything *)
  Definition decode : uaction reg_t empty_ext_fn_t :=
    {{
        let instr := fromIMem.(MemResp.deq)() in
        let instr := get(instr,data) in
        let fetched_bookeeping := f2d.(fromFetch.deq)() in
        let decodedInst := decode_fun(instr) in
        when (get(fetched_bookeeping, epoch) == read0(epoch)) do
             (let rs1_idx := get(getFields(instr), rs1) in
             let rs2_idx := get(getFields(instr), rs2) in
             let score := Ob~0~0 in
             if (get(decodedInst, valid_rs1)) then
               set score := (score + scoreboard.(Scoreboard.search)(rs1_idx))
             else
               if (get(decodedInst, valid_rs2)) then
                 set score := (score + scoreboard.(Scoreboard.search)(rs2_idx))
               else pass;
             guard (score == Ob~0~0);
             (when (get(decodedInst, valid_rd)) do
                  let rd_idx := get(getFields(instr), rd) in
                  scoreboard.(Scoreboard.insert)(rd_idx));
             let rs1 := rf.(Rf.read)(rs1_idx) in
             let rs2 := rf.(Rf.read)(rs2_idx) in
             let decode_bookkeeping := struct decode_bookkeeping {|
                                                pc    := get(fetched_bookeeping, pc);
                                                ppc   := get(fetched_bookeeping, ppc);
                                                epoch := get(fetched_bookeeping, epoch);
                                                dInst := decodedInst;
                                                rval1 := rs1;
                                                rval2 := rs2
                                              |} in
             d2e.(fromDecode.enq)(decode_bookkeeping))
    }}.

  Definition tc_decode:=
    tc_action R empty_Sigma decode.

  (* Useful for debugging *)
  Arguments Var {pos_t var_t reg_t ext_fn_t R Sigma sig} k {tau m} : assert.

  Definition isMemoryInst : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun (dInst: struct_t decoded_sig) : bits_t 1 =>
          (get(dInst,inst)[|5`d6|] == Ob~0) && (get(dInst,inst)[|5`d3|:+2] == Ob~0~0)
    }}.

  Definition isControlInst : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun (dInst: struct_t decoded_sig) : bits_t 1 =>
          get(dInst,inst)[|5`d4| :+ 3] == Ob~1~1~0
    }}.

  Definition execute : uaction reg_t empty_ext_fn_t :=
    {{
        let decoded_bookeeping := d2e.(fromDecode.deq)() in
        if get(decoded_bookeeping, epoch) == read0(epoch) then
          (* By then we guarantee that this instruction is correct-path *)
          let dInst := get(decoded_bookeeping, dInst) in
          if get(dInst, legal) == Ob~0 then
            (* Always say that we had a misprediction in this case for
            simplicity *)
            write0(epoch, read0(epoch)+Ob~1);
            write0(pc, |32`d0|)
          else
            (let imm := getImmediate(dInst) in
             let pc := get(decoded_bookeeping, pc) in
             let fInst := get(dInst, inst) in
             let rs1_val := get(decoded_bookeeping, rval1) in
             let rs2_val := get(decoded_bookeeping, rval2) in
             let data := execALU32(fInst, rs1_val, rs2_val, imm, pc) in
             let isUnsigned := Ob~0 in
             let funct3 := get(getFields(fInst), funct3) in
             let size := funct3[|2`d0| :+ 2] in
             let addr := rs1_val + imm in
             let offset := addr[|5`d0| :+ 2] in
             if isMemoryInst(dInst) then
               let shift_amount := offset ++ |3`d0| in
               let byte_en := match size with
                              | Ob~0~0 => Ob~0~0~0~1
                              | Ob~0~1 => Ob~0~0~1~1
                              | Ob~1~0 => Ob~1~1~1~1
                              return default: fail(4)
                              end << offset in
               set data := rs2_val << shift_amount;
               set addr := addr[|5`d2| :+ 30 ] ++ |2`d0|;
               set isUnsigned := funct3[|2`d2|];
               let type_mem := if (fInst[|5`d5|] == Ob~1)
                               then byte_en
                               else Ob~0~0~0~0 in
               let req := struct mem_req {|
                                   byte_en := type_mem;
                                   addr := addr;
                                   data := data |} in
               toDMem.(MemReq.enq)(req)
             else if (isControlInst(dInst)) then
                    set data := (pc + |32`d4|)     (* For jump and link *)
                  else pass;
             let controlResult := execControl32(fInst, rs1_val, rs2_val, imm, pc) in
             let nextPc := get(controlResult,nextPC) in
             if !(nextPc == get(decoded_bookeeping, ppc)) then
               write0(epoch, read0(epoch)+Ob~1);
               write0(pc, nextPc)
             else
               pass;
             let execute_bookkeeping := struct execute_bookkeeping {|
                                                 isUnsigned := isUnsigned;
                                                 size := size;
                                                 offset := offset;
                                                 newrd := data;
                                                 dInst := get(decoded_bookeeping, dInst)
                                               |} in
             e2w.(fromExecute.enq)(execute_bookkeeping))
        else
          pass
    }}.

  Time Definition tc_execute :=
    tc_action R empty_Sigma execute.

  Definition writeback : uaction reg_t empty_ext_fn_t :=
    {{
        let execute_bookeeping := e2w.(fromExecute.deq)() in
        let dInst := get(execute_bookeeping, dInst) in
        let data := get(execute_bookeeping, newrd) in
        let fields := getFields(get(dInst, inst)) in
        if isMemoryInst(dInst) then (* // write_val *)
          (* Byte enable shifting back *)
          let resp := fromDMem.(MemResp.deq)() in
          let mem_data := get(resp,data) in
          set mem_data := mem_data >> (get(execute_bookeeping,offset) ++ Ob~0~0~0);
          match (get(execute_bookeeping,isUnsigned)++get(execute_bookeeping,size)) with
          | Ob~0~0~0 => set data := {signExtend 8  24}(mem_data[|5`d0|:+8])
          | Ob~0~0~1 => set data := {signExtend 16 16}(mem_data[|5`d0|:+16])
          | Ob~1~0~0 => set data := zeroExtend(mem_data[|5`d0|:+8],32)
          | Ob~1~0~1 => set data := zeroExtend(mem_data[|5`d0|:+16],32)
          | Ob~0~1~0 => set data := mem_data      (* Load Word *)
          return default: fail                   (* Load Double or Signed Word *)
          end
        else
          pass;
        if get(dInst,valid_rd) then
          let rd_idx := get(fields,rd) in
          scoreboard.(Scoreboard.remove)(rd_idx);
          if (rd_idx == |5`d0|)
          then pass
          else rf.(Rf.write)(rd_idx,data)
        else
          pass
    }}.

  Time Definition tc_writeback :=
    tc_action R empty_Sigma writeback.

  Definition externalI_environment : uaction reg_t empty_ext_fn_t :=
    {{
        let readRequestI := toIMem.(MemReq.deq)() in
        let IAddress := get(readRequestI, addr) in
        let IEn := get(readRequestI, byte_en) in
        fromIMem.(MemResp.enq)(struct mem_resp {|byte_en := IEn ; addr := IAddress; data := |32`d0| |})
    }}.

  Time Definition tc_externalI :=
    tc_action R empty_Sigma externalI_environment.

  Definition externalD_environment : uaction reg_t empty_ext_fn_t :=
    {{
        let readRequestD := toDMem.(MemReq.deq)() in
        let DAddress := get(readRequestD, addr) in
        let DEn := get(readRequestD, byte_en) in
        fromDMem.(MemResp.enq)(struct mem_resp {|byte_en := DEn ; addr := DAddress; data := |32`d0| |})
    }}.

  Time Definition tc_externalD :=
    tc_action R empty_Sigma externalD_environment.

  Inductive rv_rules_t := Fetch | Decode | Execute | Writeback | ExternalI | ExternalD.

  Definition rv_rules (rl:rv_rules_t) : rule R empty_Sigma:=
    match rl with
    | Fetch     => tc_fetch
    | Decode    => tc_decode
    | Execute   => tc_execute
    | Writeback => tc_writeback
    | ExternalI => tc_externalI
    | ExternalD => tc_externalD
    end.

  Instance FiniteType_toIMem : FiniteType MemReq.reg_t := _.
  Instance FiniteType_fromIMem : FiniteType MemResp.reg_t := _.
  Instance FiniteType_toDMem : FiniteType MemReq.reg_t := _.
  Instance FiniteType_fromDMem : FiniteType MemResp.reg_t := _.
  Instance FiniteType_f2d : FiniteType fromFetch.reg_t := _.
  Instance FiniteType_d2e : FiniteType fromDecode.reg_t := _.
  Instance FiniteType_e2w : FiniteType fromExecute.reg_t := _.
  Instance FiniteType_rf : FiniteType Rf.reg_t := _.
  Instance FiniteType_scoreboard_rf : FiniteType Scoreboard.Rf.reg_t := _.
  Instance FiniteType_scoreboard : FiniteType Scoreboard.reg_t := _.
  Instance FiniteType_reg_t : FiniteType reg_t := _.
  Definition cr := ContextEnv.(create) r.
End RV32ICore.
