import Mathlib.Tactic

namespace ToyISA

structure Registers :=
  (accumulator instruction_register program_counter memory_address_register memory_buffer_register : ℕ)

def Memory := ℕ → ℕ

inductive Instruction
| LOAD (addr : ℕ)
| STORE (addr : ℕ)
| ADD (addr : ℕ)
| SUB (addr : ℕ)
| JMP (addr : ℕ)
| JZ (addr : ℕ)
| NOP
| HALT

-- Decodes the instruction at the instruction register.
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
  | _ => Instruction.HALT

-- Loads a value from memory at the address specified by the memory address register.
def load_from_memory (regs : Registers) (mem : Memory) : Registers × Memory :=
  let addr := regs.memory_address_register
  let value := mem addr
  ({ accumulator := regs.accumulator,
     instruction_register := regs.instruction_register,
     program_counter := regs.program_counter,
     memory_address_register := regs.memory_address_register,
     memory_buffer_register := value }, mem)

-- Stores a value in memory at the address specified by the memory address register.
def store_to_memory (regs : Registers) (mem : Memory) : Registers × Memory :=
  let addr := regs.memory_address_register
  let value := regs.memory_buffer_register
  let new_mem := λ n => if n = addr then value else mem n
  (regs, new_mem)

-- Executes a subinstruction for loading from memory.
def execute_load_from_memory_subinstruction (addr : ℕ) (regs : Registers) (mem : Memory) : Registers × Memory :=
  let regs_with_mar :=
    { accumulator := regs.accumulator,
      instruction_register := regs.instruction_register,
      program_counter := regs.program_counter,
      memory_address_register := addr,
      memory_buffer_register := regs.memory_buffer_register }
  load_from_memory regs_with_mar mem

-- Executes an instruction based on the decoded instruction.
def execute_instruction (instr : Instruction) (regs : Registers) (mem : Memory) : Registers × Memory :=
  match instr with
  | Instruction.LOAD addr =>
    let (regs_loaded, mem_loaded) := execute_load_from_memory_subinstruction addr regs mem
    ({ accumulator := regs_loaded.memory_buffer_register,
       instruction_register := regs_loaded.instruction_register,
       program_counter := regs_loaded.program_counter,
       memory_address_register := regs_loaded.memory_address_register,
       memory_buffer_register := regs_loaded.memory_buffer_register }, mem_loaded)
  | Instruction.STORE addr =>
    let regs_with_mar_mbr :=
      { accumulator := regs.accumulator,
        instruction_register := regs.instruction_register,
        program_counter := regs.program_counter,
        memory_address_register := addr,
        memory_buffer_register := regs.accumulator }
    let (regs_stored, mem_stored) := store_to_memory regs_with_mar_mbr mem
    ({ accumulator := regs_stored.accumulator,
       instruction_register := regs_stored.instruction_register,
       program_counter := regs_stored.program_counter,
       memory_address_register := regs_stored.memory_address_register,
       memory_buffer_register := regs_stored.memory_buffer_register }, mem_stored)
  | Instruction.ADD addr =>
    let (regs_loaded, mem_loaded) := execute_load_from_memory_subinstruction addr regs mem
    ({ accumulator := regs_loaded.accumulator + regs_loaded.memory_buffer_register,
       instruction_register := regs_loaded.instruction_register,
       program_counter := regs_loaded.program_counter,
       memory_address_register := regs_loaded.memory_address_register,
       memory_buffer_register := regs_loaded.memory_buffer_register }, mem_loaded)
  | Instruction.SUB addr =>
    let (regs_loaded, mem_loaded) := execute_load_from_memory_subinstruction addr regs mem
    ({ accumulator := regs_loaded.accumulator - regs_loaded.memory_buffer_register,
       instruction_register := regs_loaded.instruction_register,
       program_counter := regs_loaded.program_counter,
       memory_address_register := regs_loaded.memory_address_register,
       memory_buffer_register := regs_loaded.memory_buffer_register }, mem_loaded)
  | Instruction.JMP addr =>
    ({ accumulator := regs.accumulator,
       instruction_register := regs.instruction_register,
       program_counter := addr,
       memory_address_register := regs.memory_address_register,
       memory_buffer_register := regs.memory_buffer_register }, mem)
  | Instruction.JZ addr =>
    if regs.accumulator = 0 then
      ({ accumulator := regs.accumulator,
         instruction_register := regs.instruction_register,
         program_counter := addr,
         memory_address_register := regs.memory_address_register,
         memory_buffer_register := regs.memory_buffer_register }, mem)
    else
      ({ accumulator := regs.accumulator,
         instruction_register := regs.instruction_register,
         program_counter := regs.program_counter,
         memory_address_register := regs.memory_address_register,
         memory_buffer_register := regs.memory_buffer_register }, mem)
  | Instruction.NOP =>
    ({ accumulator := regs.accumulator,
       instruction_register := regs.instruction_register,
       program_counter := regs.program_counter,
       memory_address_register := regs.memory_address_register,
       memory_buffer_register := regs.memory_buffer_register }, mem)
  | Instruction.HALT => (regs, mem)

-- Fetches the instruction from memory at the program counter.
def fetch_instruction (regs : Registers) (mem : Memory) : Registers :=
  let pc := regs.program_counter
  let encoded_instr := mem pc
  { accumulator := regs.accumulator,
    instruction_register := encoded_instr,
    program_counter := regs.program_counter,
    memory_address_register := regs.memory_address_register,
    memory_buffer_register := regs.memory_buffer_register }

inductive TerminationStatus
| NormalTermination
| FuelExhausted

-- Executes a single cycle of the processor.
def execute_single_cycle (regs : Registers) (mem : Memory) : Registers × Memory :=
  let fetched_regs := fetch_instruction regs mem
  let instr := decode_instruction fetched_regs mem
  let pc_increment :=
    match instr with
    | Instruction.LOAD _ | Instruction.STORE _ | Instruction.ADD _ | Instruction.SUB _ | Instruction.JMP _ | Instruction.JZ _ => 2
    | Instruction.NOP | Instruction.HALT => 1
  let updated_regs :=
    { accumulator := fetched_regs.accumulator,
      instruction_register := fetched_regs.instruction_register,
      program_counter := fetched_regs.program_counter + pc_increment,
      memory_address_register := fetched_regs.memory_address_register,
      memory_buffer_register := fetched_regs.memory_buffer_register }
  match instr with
  | Instruction.HALT => (updated_regs, mem)
  | _ => execute_instruction instr updated_regs mem

-- Executes multiple cycles with a fuel limit.
def execute_cycles (regs : Registers) (mem : Memory) (fuel : ℕ) : Registers × Memory × TerminationStatus :=
  match fuel with
  | 0 => (regs, mem, TerminationStatus.FuelExhausted)
  | Nat.succ fuel' =>
    let (new_regs, new_mem) := execute_single_cycle regs mem
    match new_regs.instruction_register with
    | 1 => (new_regs, new_mem, TerminationStatus.NormalTermination)
    | _ => execute_cycles new_regs new_mem fuel'

-- Checks if the program halts within the given fuel limit.
def program_halts (initial_regs : Registers) (mem : Memory) (fuel : ℕ) : Bool :=
  let (_, _, status) := execute_cycles initial_regs mem fuel
  match status with
  | TerminationStatus.NormalTermination => true
  | TerminationStatus.FuelExhausted => false

end ToyISA


-- EXAMPLE PROGRAM 1: Dummy Program

namespace ExampleProgram1

open ToyISA

-- Example initial registers.
def example_1_regs : Registers :=
  { accumulator := 0,
    instruction_register := 0,
    program_counter := 0,
    memory_address_register := 0,
    memory_buffer_register := 0 }

-- Example memory contents.
def example_1_memory : Memory :=
  λ addr =>
    match addr with
    | 0 => 0
    | 1 => 2
    | 2 => 5
    | 3 => 6
    | 4 => 6
    | 5 => 42
    | 6 => 1
    | _ => 0

-- Example fuel limit.
def example_1_fuel_limit : ℕ := 10

-- Check if the example program halts within the given fuel limit.
def example_1_program_halts : Bool :=
  program_halts example_1_regs example_1_memory example_1_fuel_limit

end ExampleProgram1
