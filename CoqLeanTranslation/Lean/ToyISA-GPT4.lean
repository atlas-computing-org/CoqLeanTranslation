-- Lean equivalent of Coq's `nat`
@[reducible]
def Register := Nat

-- Record in Lean for Toy_ISA_Registers
structure Toy_ISA_Registers :=
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
def decode_instruction (regs : Toy_ISA_Registers) (mem : Memory) : Instruction :=
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
def load_from_memory (regs : Toy_ISA_Registers) (mem : Memory) : Toy_ISA_Registers × Memory :=
  let addr := regs.memory_address_register
  let value := mem addr
  ({regs with memory_buffer_register := value}, mem)

-- Function to store a value from the MBR into memory
def store_to_memory (regs : Toy_ISA_Registers) (mem : Memory) : Toy_ISA_Registers × Memory :=
  let addr := regs.memory_address_register
  let value := regs.memory_buffer_register
  let new_mem := fun n => if n = addr then value else mem n
  (regs, new_mem)

-- Function to execute the common subinstruction of loading from memory
def execute_load_from_memory_subinstruction (addr : Nat) (regs : Toy_ISA_Registers) (mem : Memory) : Toy_ISA_Registers × Memory :=
  let regs_with_mar := {regs with memory_address_register := addr}
  load_from_memory regs_with_mar mem

-- Function to execute a single instruction
def execute_instruction (instr : Instruction) (regs : Toy_ISA_Registers) (mem : Memory) : Toy_ISA_Registers × Memory :=
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
def fetch_instruction (regs : Toy_ISA_Registers) (mem : Memory) : Toy_ISA_Registers :=
  let pc := regs.program_counter
  let encoded_instr := mem pc
  {regs with instruction_register := encoded_instr}

-- Function to execute a single cycle
def execute_single_cycle (regs : Toy_ISA_Registers) (mem : Memory) : Toy_ISA_Registers × Memory :=
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
def execute_cycles (regs : Toy_ISA_Registers) (mem : Memory) (fuel : Nat) : Toy_ISA_Registers × Memory × TerminationStatus :=
  match fuel with
  | 0 => (regs, mem, TerminationStatus.FuelExhausted)
  | fuel' + 1 =>
      let (new_regs, new_mem) := execute_single_cycle regs mem
      match new_regs.instruction_register with
      | 1 => (new_regs, new_mem, TerminationStatus.NormalTermination)
      | _ => execute_cycles new_regs new_mem fuel'

-- Function to check if a program halts within a specified fuel limit
def program_halts (initial_regs : Toy_ISA_Registers) (mem : Memory) (fuel : Nat) : Bool :=
  let (_, _, status) := execute_cycles initial_regs mem fuel
  match status with
  | TerminationStatus.NormalTermination => true
  | TerminationStatus.FuelExhausted => false


-- EXAMPLE PROGRAM 1: Dummy Program

def example_1_regs : Toy_ISA_Registers :=
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
