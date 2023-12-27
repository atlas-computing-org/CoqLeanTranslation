Definition Register := nat.

Record Registers := {
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
Definition decode_instruction (regs: Registers) (mem: Memory) : Instruction :=
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
Definition load_from_memory (regs: Registers) (mem: Memory) : Registers * Memory :=
  let addr := regs.(memory_address_register) in
  let value := mem addr in
  ({| accumulator := regs.(accumulator);
      instruction_register := regs.(instruction_register);
      program_counter := regs.(program_counter);
      memory_address_register := regs.(memory_address_register);
      memory_buffer_register := value |}, mem).

(* Function to store a value from the MBR into memory *)
Definition store_to_memory (regs: Registers) (mem: Memory) : Registers * Memory :=
  let addr := regs.(memory_address_register) in
  let value := regs.(memory_buffer_register) in
  let new_mem := fun n => if Nat.eqb n addr then value else mem n in
  (regs, new_mem).

(* Function to execute the common subinstruction of loading from memory *)
Definition execute_load_from_memory_subinstruction (addr: nat) (regs: Registers) (mem: Memory) : Registers * Memory :=
  let regs_with_mar := {| accumulator := regs.(accumulator);
                          instruction_register := regs.(instruction_register);
                          program_counter := regs.(program_counter);
                          memory_address_register := addr;
                          memory_buffer_register := regs.(memory_buffer_register) |} in
  load_from_memory regs_with_mar mem.

(* Function to execute a single instruction *)
Definition execute_instruction (instr: Instruction) (regs: Registers) (mem: Memory) : Registers * Memory :=
  match instr with
  | LOAD addr =>
      let (regs_loaded, mem_loaded) := execute_load_from_memory_subinstruction addr regs mem in
      ({| accumulator := regs_loaded.(memory_buffer_register);
          instruction_register := regs_loaded.(instruction_register);
          program_counter := regs_loaded.(program_counter);
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
          program_counter := regs_stored.(program_counter);
          memory_address_register := regs_stored.(memory_address_register);
          memory_buffer_register := regs_stored.(memory_buffer_register) |}, mem_stored)
  | ADD addr =>
      let (regs_loaded, mem_loaded) := execute_load_from_memory_subinstruction addr regs mem in
      ({| accumulator := regs_loaded.(accumulator) + regs_loaded.(memory_buffer_register);
          instruction_register := regs_loaded.(instruction_register);
          program_counter := regs_loaded.(program_counter);
          memory_address_register := regs_loaded.(memory_address_register);
          memory_buffer_register := regs_loaded.(memory_buffer_register) |}, mem_loaded)
  | SUB addr =>
      let (regs_loaded, mem_loaded) := execute_load_from_memory_subinstruction addr regs mem in
      ({| accumulator := regs_loaded.(accumulator) - regs_loaded.(memory_buffer_register);
          instruction_register := regs_loaded.(instruction_register);
          program_counter := regs_loaded.(program_counter);
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
            program_counter := regs.(program_counter);
            memory_address_register := regs.(memory_address_register);
            memory_buffer_register := regs.(memory_buffer_register) |}, mem)
  | NOP =>
      ({| accumulator := regs.(accumulator);
          instruction_register := regs.(instruction_register);
          program_counter := regs.(program_counter);
          memory_address_register := regs.(memory_address_register);
          memory_buffer_register := regs.(memory_buffer_register) |}, mem)
  | HALT =>
      (regs, mem)
  end.

Definition fetch_instruction (regs: Registers) (mem: Memory) : Registers :=
  let pc := regs.(program_counter) in
  let encoded_instr := mem pc in
  {| accumulator := regs.(accumulator);
     instruction_register := encoded_instr;
     program_counter := regs.(program_counter);
     memory_address_register := regs.(memory_address_register);
     memory_buffer_register := regs.(memory_buffer_register) |}.

(* Function to execute a single cycle *)
Definition execute_single_cycle (regs: Registers) (mem: Memory) : Registers * Memory :=
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
Fixpoint execute_cycles (regs: Registers) (mem: Memory) (fuel: nat)
  : (Registers * Memory * TerminationStatus) :=
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
Definition program_halts (initial_regs: Registers) (mem: Memory) (fuel: nat) : bool :=
  let '(_, _, status) := execute_cycles initial_regs mem fuel in
  match status with
  | NormalTermination => true
  | FuelExhausted => false
  end.


(*** EXAMPLE PROGRAM 1: Dummy Program ***)

(* Initial state of the registers in the example program *)
Definition example_1_regs : Registers :=
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


(*** EXAMPLE PROGRAM 2: Sum a List of Integers ***)

(* Initial state of the registers in the example program *)
Definition example_2_regs : Registers :=
  {| accumulator := 0;
     instruction_register := 0;
     program_counter := 0;
     memory_address_register := 0;
     memory_buffer_register := 0 |}.

(**
 * Memory layout:
 * - Program instructions
 *   - Set num remaining input values to num input values
 *   - Set next input value address to program input start address + 1
 *   - While num remaining input values is more than 0
 *     - Load value at next input value address
 *     - Add value at current sum value
 *     - Store value to current sum value
 *     - Decrement num remaining input values
 *     - Increment next input value address
 *   - Halt
 * - Program data and initial values
 *   - Constant value 1 := 1
 *   - Num remaining input values := dummy
 *   - Next input value address := program input start address
 *   - Current sum := 0
 * - Program output
 *   - Current sum (reuse the program data variable)
 * - Program input
 *   - Num input values
 *   - List of input values
 *)

(* Initial example program in memory, which must be composed with the program input in memory *)
Definition example_2_program_memory : Memory :=
  let START_OF_LOOP := 10 in
  let PTR_NEXT_INPUT_VALUE := 19 in
  let LAST_PROGRAM_INSTRUCTION := 38 in
  let program_data_start := LAST_PROGRAM_INSTRUCTION + 1 in

  let const_1 :=                    program_data_start + 0 in
  let num_remaining_input_values := program_data_start + 1 in
  let next_input_value_addr :=      program_data_start + 2 in
  let current_sum :=                program_data_start + 3 in
  let program_input_start :=        program_data_start + 4 in

  let dummy_value := 0 in
  let init_num_remaining_input_values := dummy_value in
  let init_next_input_value_addr := program_input_start in
  let init_current_sum_value := 0 in

  fun addr =>
    match addr with
    (** PROGRAM INSTRUCTIONS **)

    (* Set num remaining input values to num input values *)
    | 0 => 2    (* LOAD first input value *)
    | 1 => program_input_start
    | 2 => 3    (* STORE num remaining input values *)
    | 3 => num_remaining_input_values

    (* Set next input value address to program input start address + 1 *)
    | 4 => 2    (* LOAD next input value address *)
    | 5 => next_input_value_addr
    | 6 => 4    (* ADD 1 *)
    | 7 => const_1
    | 8 => 3    (* STORE next input value address *)
    | 9 => next_input_value_addr

    (* LOOP: While num remaining input values is more than 0 *)
    (* START_OF_LOOP: 10 *)
    | 10 => 2   (* LOAD num remaining input values *)
    | 11 => num_remaining_input_values
    | 12 => 7   (* JZ last program instruction *)
    | 13 => LAST_PROGRAM_INSTRUCTION

    (* Load value at next input value address *)
    | 14 => 2   (* LOAD next input value address *)
    | 15 => next_input_value_addr
    | 16 => 3   (* STORE pointer to next input value *)
    | 17 => PTR_NEXT_INPUT_VALUE
    | 18 => 2   (* LOAD next input value *)
    (* PTR_NEXT_INPUT_VALUE: 19 *)
    | 19 => dummy_value

    (* Add value at current sum value *)
    | 20 => 4   (* ADD current sum *)
    | 21 => current_sum

    (* Store value to current sum value *)
    | 22 => 3   (* STORE current sum *)
    | 23 => current_sum

    (* Decrement num remaining input values *)
    | 24 => 2   (* LOAD num remaining input values *)
    | 25 => num_remaining_input_values
    | 26 => 5   (* SUB 1 *)
    | 27 => const_1
    | 28 => 3   (* STORE num remaining input values *)
    | 29 => num_remaining_input_values

    (* Increment next input value address *)
    | 30 => 2   (* LOAD next input value address *)
    | 31 => next_input_value_addr
    | 32 => 4   (* ADD 1 *)
    | 33 => const_1
    | 34 => 3   (* STORE next input value address *)
    | 35 => next_input_value_addr

    (* Jump to start of loop *)
    | 36 => 6   (* JMP start of loop *)
    | 37 => START_OF_LOOP

    (* END LOOP *)

    (* Halt *)
    (* LAST_PROGRAM_INSTRUCTION: 38 *)
    | 38 => 1   (* HALT *)

    (** END PROGRAM INSTRUCTIONS **)

    (** PROGRAM DATA **)
    | 39 => 1                                 (* const_1 *)
    | 40 => init_num_remaining_input_values   (* num_remaining_input_values *)
    | 41 => init_next_input_value_addr        (* next_input_value_addr *)
    | 42 => init_current_sum_value            (* current_sum *)

    (* 43: program_input_start *)

    | _ => 0  (* Default value for other addresses *)
    end.

Definition example_2_return_value_addr : nat := 42.
Definition example_2_program_memory_size : nat := 43.

(* Initial memory in the example program *)
Definition example_2_input_memory : Memory :=
  fun addr =>
    match addr with
    | 0 => 5
    | 1 => 9
    | 2 => 5
    | 3 => 8
    | 4 => 6
    | 5 => 4
    | _ => 1  (* Default value for other addresses *)
    end.

Fixpoint is_less_than (n m : nat) : bool :=
  match n, m with
  | _, 0 => false
  | 0, S _ => true
  | S n', S m' => is_less_than n' m'
  end.

(* Initial memory in the example program *)
Definition example_2_memory : Memory :=
  fun addr =>
    let is_program_memory:bool := is_less_than addr example_2_program_memory_size in
    if is_program_memory then
      example_2_program_memory addr
    else
      example_2_input_memory (addr - example_2_program_memory_size).

(* Fuel limit for analyzing the example program *)
Definition example_2_fuel_limit := 100.

(* Check if the example program halts *)
Definition example_2_program_halts : bool :=
  program_halts example_2_regs example_2_memory example_2_fuel_limit.

(* Calculate the return value of the example program *)
Definition example_2_return_value : nat :=
  let '(_, m, _) := execute_cycles example_2_regs example_2_memory example_2_fuel_limit in
  m example_2_return_value_addr.
