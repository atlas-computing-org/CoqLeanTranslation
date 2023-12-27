Definition Register := nat.

Record Toy_ISA_Registers := {
  accumulator : Register;
  instruction_register : Register;
  program_counter : Register;
  memory_address_register : Register;
  memory_buffer_register : Register
}.

Definition Memory := nat -> nat.  (* A function representing memory as an array of natural numbers *)
  
Inductive Instruction :=
  | LOAD (addr: nat)
  | STORE (addr: nat)
  | ADD (addr: nat)
  | SUB (addr: nat)
  | JMP (addr: nat)
  | JZ (addr: nat)
  | NOP
  | HALT.

(* Function to decode an instruction from the instruction register *)
Definition decode_instruction (regs: Toy_ISA_Registers) (mem: Memory) : Instruction :=
  let encoded_instr := regs.(instruction_register) in
  match encoded_instr with
  | 0 => NOP
  | 1 => HALT
  | 2 => LOAD (mem (regs.(program_counter) + 1))
  | 3 => STORE (mem (regs.(program_counter) + 1))
  | 4 => ADD (mem (regs.(program_counter) + 1))
  | 5 => SUB (mem (regs.(program_counter) + 1))
  | 6 => JMP (mem (regs.(program_counter) + 1))
  | 7 => JZ (mem (regs.(program_counter) + 1))
  | _ => HALT (* Default case for undefined instructions *)
  end.

(* Function to load a value from memory into the MBR *)
Definition load_from_memory (regs: Toy_ISA_Registers) (mem: Memory) : Toy_ISA_Registers * Memory :=
  let addr := regs.(memory_address_register) in
  let value := mem addr in
  ({| accumulator := regs.(accumulator);
      instruction_register := regs.(instruction_register);
      program_counter := regs.(program_counter);
      memory_address_register := regs.(memory_address_register);
      memory_buffer_register := value |}, mem).

(* Function to store a value from the MBR into memory *)
Definition store_to_memory (regs: Toy_ISA_Registers) (mem: Memory) : Toy_ISA_Registers * Memory :=
  let addr := regs.(memory_address_register) in
  let value := regs.(memory_buffer_register) in
  let new_mem := fun n => if Nat.eqb n addr then value else mem n in
  (regs, new_mem).

(* Function to execute the common subinstruction of loading from memory *)
Definition execute_load_from_memory_subinstruction (addr: nat) (regs: Toy_ISA_Registers) (mem: Memory) : Toy_ISA_Registers * Memory :=
  let regs_with_mar := {| accumulator := regs.(accumulator);
                          instruction_register := regs.(instruction_register);
                          program_counter := regs.(program_counter);
                          memory_address_register := addr;
                          memory_buffer_register := regs.(memory_buffer_register) |} in
  load_from_memory regs_with_mar mem.

(* Function to execute a single instruction *)
Definition execute_instruction (instr: Instruction) (regs: Toy_ISA_Registers) (mem: Memory) : Toy_ISA_Registers * Memory :=
  match instr with
  | LOAD addr => 
      let (regs_loaded, mem_loaded) := execute_load_from_memory_subinstruction addr regs mem in
      ({| accumulator := regs_loaded.(memory_buffer_register);
          instruction_register := regs_loaded.(instruction_register);
          program_counter := regs_loaded.(program_counter) + 1;
          memory_address_register := regs_loaded.(memory_address_register);
          memory_buffer_register := regs_loaded.(memory_buffer_register) |}, mem_loaded)
  | STORE addr =>
      let regs_with_mar_mbr := {|
          accumulator := regs.(accumulator);
          instruction_register := regs.(instruction_register);
          program_counter := regs.(program_counter);
          memory_address_register := addr;
          memory_buffer_register := regs.(accumulator) |} in
      let (regs_stored, mem_stored) := store_to_memory regs_with_mar_mbr mem in
      ({| accumulator := regs_stored.(accumulator);
          instruction_register := regs_stored.(instruction_register);
          program_counter := regs_stored.(program_counter) + 1;
          memory_address_register := regs_stored.(memory_address_register);
          memory_buffer_register := regs_stored.(memory_buffer_register) |}, mem_stored)
  | ADD addr =>
      let (regs_loaded, mem_loaded) := execute_load_from_memory_subinstruction addr regs mem in
      ({| accumulator := regs_loaded.(accumulator) + regs_loaded.(memory_buffer_register);
          instruction_register := regs_loaded.(instruction_register);
          program_counter := regs_loaded.(program_counter) + 1;
          memory_address_register := regs_loaded.(memory_address_register);
          memory_buffer_register := regs_loaded.(memory_buffer_register) |}, mem_loaded)
  | SUB addr =>
      let (regs_loaded, mem_loaded) := execute_load_from_memory_subinstruction addr regs mem in
      ({| accumulator := regs_loaded.(accumulator) - regs_loaded.(memory_buffer_register);
          instruction_register := regs_loaded.(instruction_register);
          program_counter := regs_loaded.(program_counter) + 1;
          memory_address_register := regs_loaded.(memory_address_register);
          memory_buffer_register := regs_loaded.(memory_buffer_register) |}, mem_loaded)
  | JMP addr =>
      ({| accumulator := regs.(accumulator);
          instruction_register := regs.(instruction_register);
          program_counter := addr;
          memory_address_register := regs.(memory_address_register);
          memory_buffer_register := regs.(memory_buffer_register) |}, mem)
  | JZ addr =>
      if Nat.eqb regs.(accumulator) 0 then
        ({| accumulator := regs.(accumulator);
            instruction_register := regs.(instruction_register);
            program_counter := addr;
            memory_address_register := regs.(memory_address_register);
            memory_buffer_register := regs.(memory_buffer_register) |}, mem)
      else
        ({| accumulator := regs.(accumulator);
            instruction_register := regs.(instruction_register);
            program_counter := regs.(program_counter) + 1;
            memory_address_register := regs.(memory_address_register);
            memory_buffer_register := regs.(memory_buffer_register) |}, mem)
  | NOP =>
      ({| accumulator := regs.(accumulator);
          instruction_register := regs.(instruction_register);
          program_counter := regs.(program_counter) + 1;
          memory_address_register := regs.(memory_address_register);
          memory_buffer_register := regs.(memory_buffer_register) |}, mem)
  | HALT =>
      (regs, mem)
  end.

Definition fetch_instruction (regs: Toy_ISA_Registers) (mem: Memory) : Toy_ISA_Registers :=
  let pc := regs.(program_counter) in
  let encoded_instr := mem pc in
  {| accumulator := regs.(accumulator);
     instruction_register := encoded_instr;
     program_counter := regs.(program_counter );
     memory_address_register := regs.(memory_address_register);
     memory_buffer_register := regs.(memory_buffer_register) |}.

(* Function to execute a single cycle *)
Definition execute_single_cycle (regs: Toy_ISA_Registers) (mem: Memory) : Toy_ISA_Registers * Memory :=
    let fetched_regs := fetch_instruction regs mem in
    let instr := decode_instruction fetched_regs mem in
    let pc_increment := match instr with
                        | LOAD _ | STORE _ | ADD _ | SUB _ | JMP _ | JZ _ => 2  (* Instructions with an operand *)
                        | NOP | HALT => 1  (* Instructions without an operand *)
                        end in
    let updated_regs := {| accumulator := fetched_regs.(accumulator);
                          instruction_register := fetched_regs.(instruction_register);
                          program_counter := fetched_regs.(program_counter) + pc_increment;
                          memory_address_register := fetched_regs.(memory_address_register);
                          memory_buffer_register := fetched_regs.(memory_buffer_register) |} in
    match instr with
    | HALT => (updated_regs, mem)
    | _ => execute_instruction instr updated_regs mem
    end.

Inductive TerminationStatus :=
  | NormalTermination
  | FuelExhausted.

(* Recursive function to execute cycles until HALT or fuel runs out *)
Fixpoint execute_cycles (regs: Toy_ISA_Registers) (mem: Memory) (fuel: nat) 
  : (Toy_ISA_Registers * Memory * TerminationStatus) :=
  match fuel with
  | 0 => (regs, mem, FuelExhausted)  (* Termination due to fuel exhaustion *)
  | S fuel' =>
      let (new_regs, new_mem) := execute_single_cycle regs mem in
      match new_regs.(instruction_register) with
      | 1 => (new_regs, new_mem, NormalTermination)  (* HALT instruction encoded as 1 *)
      | _ => execute_cycles new_regs new_mem fuel'
      end
  end.

(* Function to check if a program halts within a specified fuel limit *)
Definition program_halts (initial_regs: Toy_ISA_Registers) (mem: Memory) (fuel: nat) : bool :=
  let '(_, _, status) := execute_cycles initial_regs mem fuel in
  match status with
  | NormalTermination => true
  | FuelExhausted => false
  end.


(*** EXAMPLE PROGRAM 1: Dummy Program ***)

(* Initial state of the registers in the example program *)
Definition example_1_regs : Toy_ISA_Registers :=
  {| accumulator := 0;
     instruction_register := 0;
     program_counter := 0;
     memory_address_register := 0;
     memory_buffer_register := 0 |}.

(* Initial memory in the example program *)
Definition example_1_memory : Memory :=
  fun addr =>
    match addr with
    | 0 => 0  (* NOP *)
    | 1 => 2  (* LOAD *)
    | 2 => 5  (* Address 5 *)
    | 3 => 6  (* JMP *)
    | 4 => 6  (* Address 6 *)
    | 5 => 42 (* Value to be loaded *)
    | 6 => 1  (* HALT *)
    | _ => 0  (* Default value for other addresses *)
    end.

(* Fuel limit for analyzing the example program *)
Definition example_1_fuel_limit := 10.

(* Check if the example program halts *)
Definition example_1_program_halts : bool :=
  program_halts example_1_regs example_1_memory example_1_fuel_limit.