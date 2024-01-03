namespace ToyISA

-- Lean equivalent of Coq's `nat`
@[reducible]
def Register := Nat

-- Record in Lean for Registers
structure Registers :=
  (accumulator : Register)
  (instruction_register : Register)
  (program_counter : Register)
  (memory_address_register : Register)
  (memory_buffer_register : Register)

-- Memory represented as a function from natural numbers to natural numbers
def Memory := Nat → Nat

-- Inductive type for Instruction, similar to Coq's Inductive type
inductive Instruction
  | LOAD (addr : Nat)
  | STORE (addr : Nat)
  | ADD (addr : Nat)
  | SUB (addr : Nat)
  | JMP (addr : Nat)
  | JZ (addr : Nat)
  | NOP
  | HALT

-- Function to decode an instruction from the instruction register
def decode_instruction (regs : Registers) (mem : Memory) : Instruction :=
  let encoded_instr := regs.instruction_register
  match encoded_instr with
  | 0 => Instruction.NOP
  | 1 => Instruction.HALT
  | 2 => Instruction.LOAD (mem (regs.program_counter + 1))
  | 3 => Instruction.STORE (mem (regs.program_counter + 1))
  | 4 => Instruction.ADD (mem (regs.program_counter + 1))
  | 5 => Instruction.SUB (mem (regs.program_counter + 1))
  | 6 => Instruction.JMP (mem (regs.program_counter + 1))
  | 7 => Instruction.JZ (mem (regs.program_counter + 1))
  | _ => Instruction.HALT -- Default case for undefined instructions

-- Function to load a value from memory into the MBR
def load_from_memory (regs : Registers) (mem : Memory) : Registers × Memory :=
  let addr := regs.memory_address_register
  let value := mem addr
  ({regs with memory_buffer_register := value}, mem)

-- Function to store a value from the MBR into memory
def store_to_memory (regs : Registers) (mem : Memory) : Registers × Memory :=
  let addr := regs.memory_address_register
  let value := regs.memory_buffer_register
  let new_mem := fun n => if n = addr then value else mem n
  (regs, new_mem)

-- Function to execute the common subinstruction of loading from memory
def execute_load_from_memory_subinstruction (addr : Nat) (regs : Registers) (mem : Memory) : Registers × Memory :=
  let regs_with_mar := {regs with memory_address_register := addr}
  load_from_memory regs_with_mar mem

-- Function to execute a single instruction
def execute_instruction (instr : Instruction) (regs : Registers) (mem : Memory) : Registers × Memory :=
  match instr with
  | Instruction.LOAD addr =>
      let (regs_loaded, mem_loaded) := execute_load_from_memory_subinstruction addr regs mem
      ({regs_loaded with accumulator := regs_loaded.memory_buffer_register}, mem_loaded)
  | Instruction.STORE addr =>
      let regs_with_mar_mbr := {regs with memory_address_register := addr, memory_buffer_register := regs.accumulator}
      let (regs_stored, mem_stored) := store_to_memory regs_with_mar_mbr mem
      (regs_stored, mem_stored)
  | Instruction.ADD addr =>
      let (regs_loaded, mem_loaded) := execute_load_from_memory_subinstruction addr regs mem
      ({regs_loaded with accumulator := regs_loaded.accumulator + regs_loaded.memory_buffer_register}, mem_loaded)
  | Instruction.SUB addr =>
      let (regs_loaded, mem_loaded) := execute_load_from_memory_subinstruction addr regs mem
      ({regs_loaded with accumulator := regs_loaded.accumulator - regs_loaded.memory_buffer_register}, mem_loaded)
  | Instruction.JMP addr =>
      ({regs with program_counter := addr}, mem)
  | Instruction.JZ addr =>
      if regs.accumulator = 0 then
        ({regs with program_counter := addr}, mem)
      else
        (regs, mem)
  | Instruction.NOP =>
      (regs, mem)
  | Instruction.HALT =>
      (regs, mem)

-- Function to fetch an instruction
def fetch_instruction (regs : Registers) (mem : Memory) : Registers :=
  let pc := regs.program_counter
  let encoded_instr := mem pc
  {regs with instruction_register := encoded_instr}

-- Function to execute a single cycle
def execute_single_cycle (regs : Registers) (mem : Memory) : Registers × Memory :=
  let fetched_regs := fetch_instruction regs mem
  let instr := decode_instruction fetched_regs mem
  let pc_increment := match instr with
                      | Instruction.LOAD _ | Instruction.STORE _ | Instruction.ADD _ | Instruction.SUB _ | Instruction.JMP _ | Instruction.JZ _ => 2
                      | Instruction.NOP | Instruction.HALT => 1
  let updated_regs := {fetched_regs with program_counter := fetched_regs.program_counter + pc_increment}
  match instr with
  | Instruction.HALT => (updated_regs, mem)
  | _ => execute_instruction instr updated_regs mem

-- Inductive type for TerminationStatus
inductive TerminationStatus
  | NormalTermination
  | FuelExhausted

-- Recursive function to execute cycles
def execute_cycles (regs : Registers) (mem : Memory) (fuel : Nat) : Registers × Memory × TerminationStatus :=
  match fuel with
  | 0 => (regs, mem, TerminationStatus.FuelExhausted)
  | fuel' + 1 =>
      let (new_regs, new_mem) := execute_single_cycle regs mem
      match new_regs.instruction_register with
      | 1 => (new_regs, new_mem, TerminationStatus.NormalTermination)
      | _ => execute_cycles new_regs new_mem fuel'

-- Function to check if a program halts within a specified fuel limit
def program_halts (initial_regs : Registers) (mem : Memory) (fuel : Nat) : Bool :=
  let (_, _, status) := execute_cycles initial_regs mem fuel
  match status with
  | TerminationStatus.NormalTermination => true
  | TerminationStatus.FuelExhausted => false

#eval program_halts ({accumulator := 0, instruction_register := 0, program_counter := 0, memory_address_register := 0, memory_buffer_register := 0}) (fun _ => 1) 10

theorem program_halts_iff_status_is_halts :
    ∀ (r: Registers) (m: Memory) (f: Nat),
    program_halts r m f <->
    (execute_cycles r m f).2.2 = TerminationStatus.NormalTermination := by
  intro r m n
  unfold program_halts; simp
  cases execute_cycles r m n; simp
  split
  . simp; assumption
  . simp [*]

theorem program_halts_if_memory_is_all_ones :
  ∀ (initial_regs : Registers) (f: Nat), f > 0 -> program_halts initial_regs (fun _ => 1) f := by
  intro initial_regs f h
  rw [program_halts_iff_status_is_halts]
  unfold execute_cycles
  split; try contradiction
  unfold execute_single_cycle fetch_instruction decode_instruction
  simp

end ToyISA


-- EXAMPLE PROGRAM 1: Dummy Program

namespace ExampleProgram1

open ToyISA

def example_1_regs : Registers :=
  {accumulator := 0, instruction_register := 0, program_counter := 0, memory_address_register := 0, memory_buffer_register := 0}

def example_1_memory : Memory :=
  fun addr =>
    match addr with
    | 0 => 0
    | 1 => 2
    | 2 => 5
    | 3 => 6
    | 4 => 6
    | 5 => 42
    | 6 => 1
    | _ => 0

def example_1_fuel_limit := 10

def example_1_program_halts : Bool :=
  program_halts example_1_regs example_1_memory example_1_fuel_limit

end ExampleProgram1

namespace ExampleProgram2

open ToyISA

-- Example 2: Sum a List of Integers
def example_2_regs : Registers := {
  accumulator := 0,
  instruction_register := 0,
  program_counter := 0,
  memory_address_register := 0,
  memory_buffer_register := 0
}

def example_2_program_memory : Memory :=
  let START_OF_LOOP := 10
  let PTR_NEXT_INPUT_VALUE := 19
  let LAST_PROGRAM_INSTRUCTION := 38
  let program_data_start := LAST_PROGRAM_INSTRUCTION + 1

  let const_1 := program_data_start
  let num_remaining_input_values := program_data_start + 1
  let next_input_value_addr := program_data_start + 2
  let current_sum := program_data_start + 3
  let program_input_start := program_data_start + 4

  let dummy_value := 0
  let init_num_remaining_input_values := dummy_value
  let init_next_input_value_addr := program_input_start
  let init_current_sum_value := 0

  fun addr => match addr with
    | 0 => 2    -- LOAD first input value
    | 1 => program_input_start
    | 2 => 3    -- STORE num remaining input values
    | 3 => num_remaining_input_values

    -- Set next input value address to program input start address + 1
    | 4 => 2    -- LOAD next input value address
    | 5 => next_input_value_addr
    | 6 => 4    -- ADD 1
    | 7 => const_1
    | 8 => 3    -- STORE next input value address
    | 9 => next_input_value_addr

    -- LOOP: While num remaining input values is more than 0
    -- START_OF_LOOP: 10
    | 10 => 2   -- LOAD num remaining input values
    | 11 => num_remaining_input_values
    | 12 => 7   -- JZ last program instruction
    | 13 => LAST_PROGRAM_INSTRUCTION

    -- Load value at next input value address
    | 14 => 2   -- LOAD next input value address
    | 15 => next_input_value_addr
    | 16 => 3   -- STORE pointer to next input value
    | 17 => PTR_NEXT_INPUT_VALUE
    | 18 => 2   -- LOAD next input value
    -- PTR_NEXT_INPUT_VALUE: 19
    | 19 => dummy_value

    -- Add value at current sum value
    | 20 => 4   -- ADD current sum
    | 21 => current_sum

    -- Store value to current sum value
    | 22 => 3   -- STORE current sum
    | 23 => current_sum

    -- Decrement num remaining input values
    | 24 => 2   -- LOAD num remaining input values
    | 25 => num_remaining_input_values
    | 26 => 5   -- SUB 1
    | 27 => const_1
    | 28 => 3   -- STORE num remaining input values
    | 29 => num_remaining_input_values

    -- Increment next input value address
    | 30 => 2   -- LOAD next input value address
    | 31 => next_input_value_addr
    | 32 => 4   -- ADD 1
    | 33 => const_1
    | 34 => 3   -- STORE next input value address
    | 35 => next_input_value_addr

    -- Jump to start of loop
    | 36 => 6   -- JMP start of loop
    | 37 => START_OF_LOOP

    -- END LOOP

    -- Halt
    -- LAST_PROGRAM_INSTRUCTION: 38
    | 38 => 1   -- HALT

    -- END PROGRAM INSTRUCTIONS

    -- PROGRAM DATA
    | 39 => 1                                 -- const_1
    | 40 => init_num_remaining_input_values   -- num_remaining_input_values
    | 41 => init_next_input_value_addr        -- next_input_value_addr
    | 42 => init_current_sum_value            -- current_sum

    -- 43: program_input_start

    | _ => 0  -- Default value for other addresses

def example_2_return_value_addr : Nat := 42
def example_2_program_memory_size : Nat := 43

def example_2_input_memory : Memory :=
  fun addr => match addr with
    | 0 => 5
    | 1 => 9
    | 2 => 5
    | 3 => 8
    | 4 => 6
    | 5 => 4
    | _ => 1  -- Default value for other addresses

def example_2_memory : Memory :=
  fun addr =>
    if addr < example_2_program_memory_size then
      example_2_program_memory addr
    else
      example_2_input_memory (addr - example_2_program_memory_size)

def example_2_fuel_limit : Nat := 100

def example_2_program_halts : Bool :=
  program_halts example_2_regs example_2_memory example_2_fuel_limit

-- Calculate the return value of the example program
def example_2_return_value : Nat :=
  let (_, m, _) := execute_cycles example_2_regs example_2_memory example_2_fuel_limit
  m example_2_return_value_addr

end ExampleProgram2
