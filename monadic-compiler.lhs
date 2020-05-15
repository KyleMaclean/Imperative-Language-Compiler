> import Data.Char
> import Data.List

Expression definitions

> data Expr = Val Int | Var Name | App Op Expr Expr deriving Show
> type Name = Char
> data Op = Add | Sub | Mul | Div deriving Show

Code definitions

> type Code = [Inst]
> data Inst = PUSH Int | PUSHV Name | POP Name | DO Op | JUMP Label | JUMPZ Label | LABEL Label deriving Show
> type Label = Int

Program definitions

> data Prog = Assign Name Expr | If Expr Prog Prog | While Expr Prog | Seqn [Prog] deriving Show

State Monad definitions

> type State = Label
> newtype ST a = S (State -> (a,State))
> app :: ST a -> State -> (a,State)
> app (S st) x = st x
> instance Functor ST where
>    -- fmap :: (a -> b) -> ST a -> ST b
>    fmap g st = S (\s -> let (x,s') = app st s in (g x, s'))
> instance Applicative ST where
>    -- pure :: a -> ST a
>    pure x = S (\s -> (x,s))
>    -- (<*>) :: ST (a -> b) -> ST a -> ST b
>    stf <*> stx = S (\s ->
>        let (f,s') = app stf s
>            (x,s'') = app stx s' in (f x, s''))
> instance Monad ST where
>    -- return :: a -> ST a
>    return x = S (\s -> (x,s))
>    -- (>>=) :: ST a -> (a -> ST b) -> ST b
>    st >>= f = S (\s -> let (x,s') = app st s in app (f x) s')

Virtual Machine definitions

> type Stack = [Int]
> type Mem = [(Name,Int)]

[START OF COMPILATION SECTION]

An expression has 3 (dummy) constructors, so we have 3 patterns to match and convert each into Code. The first two return a singleton list because they are the base case expressions, corresponding to a single instruction each. The last is recursive because it involves potential subexpressions and thus can build up Code consisting of multiple instructions.

> compexpr :: Expr -> Code
> compexpr (Val n) = [PUSH n]
> compexpr (Var x) = [PUSHV x]
> compexpr (App o e1 e2) = compexpr e1 ++ compexpr e2 ++ [DO o]

We accomplish simple incrementation of the state counter using a lambda. Novel labels are drawn from `fresh` in the `do` statements below and the updated state is threaded through the rest of the compilation process so that a label value greater than the last-returned one is always used. The value used is the first of the returned pair; thus for a compilation which is applied with the initial state 0, 0 will be the first label value in the Code. The final state when the compilation terminates will be 1 greater than the value of the final label in the Code.

> fresh :: ST Int
> fresh = S (\n -> (n,n+1))

Compilation of a program into its equivalent code, using the State Monad to handle generation of labels. An assignment program segment simply requires its corresponding code to be encapsulated in the state monad without adjustment to its state. The two program segments which require labels (If & While) extract them from calls to `fresh`. Although it would work for our example factorial program to just extract one label from `fresh` and then define the next label relative to that (with incrementation by 1), it would not work for bigger examples. Thus the below approach of extracting two labels from `fresh` via two explicit calls will not break for programs that need many labels. Each program segment in a sequence compiles recursively in turn, until reaching the base case of a singleton list which will match one of the non-recusrive patterns and terminate the compilation.

> compprog :: Prog -> ST Code
> compprog (Assign n e) = return (compexpr e ++ [POP n])
> compprog (If e p1 p2) = do
>                           l' <- fresh
>                           l'' <- fresh
>                           code1 <- compprog p1
>                           code2 <- compprog p2
>                           return (compexpr e
>                                ++ [JUMPZ (l')]
>                                ++ code1
>                                ++ [JUMP (l'')]
>                                ++ [LABEL l']
>                                ++ code2
>                                ++ [LABEL (l'')])
> compprog (While e p) = do
>                          l' <- fresh
>                          l'' <- fresh
>                          code <- compprog p
>                          return ([LABEL l']
>                               ++ compexpr e
>                               ++ [JUMPZ (l'')]
>                               ++ code ++ [JUMP l']
>                               ++ [LABEL (l'')])
> compprog (Seqn ps) = fmap concat (mapM compprog ps)

`compprog` is driven by `comp`, which supplies the initial state value of 0 along with the parameterised program in a call to `app`. Note that any arbitrary initial state value will work, as only the relative values of the labels are important. The result is a state monad pair of type Code, so we have to extract the first element, which is Code. There is no use in preserving the final label state.

> comp :: Prog -> Code
> comp p = fst (app (compprog p) 0)

[END OF COMPILATION SECTION]

[START OF EXECUTION SECTION]

Given a single instruction and the state of a machine (represented as a stack, memory and program counter), we execute the instruction and return the updated machine state. Pattern matching on the type of instruction allows appropriate manipulation of the machine. The functionalities of PUSH, PUSHV, POP and DO are distinguished by their respective operations on the stack and memory. The program counter is always incremented to refer to the subsequent instruction, except in the case of jump instructions, where it is assigned the location of the label to which it must jump. Accordingly, we match the program counter with a wildcard because the location of the jump instruction itself is irrelevant. The conditional jump (JUMPZ) has a simple defintion in terms of the non-conditional jump (JUMP) according to the value of the top of the stack. No action is taken when a LABEL instruction is encountered as `storeLabels` (below) handles the gathering of their information.

> execInst :: Inst -> Stack -> Mem -> Int -> (Stack,Mem,Int)
> execInst (PUSH x) s m pc = ((x:s),m,(pc+1))
> execInst (PUSHV n) s m pc = ((x:s),m,(pc+1))
>                             where (n',x) = head [(n',x) | (n',x) <- m, n' == n]
> execInst (POP n) s m pc = ((tail s),(put (n,head s) m),(pc+1))
> execInst (DO o) (y:x:s) m pc = ((((operator o) x y):s),m,(pc+1))
> execInst (JUMP l) s m _ = (s,m,pc)
>                           where (l',pc) = head [(l',pc) | (l',pc) <- m, l' == intToDigit l]
> execInst (JUMPZ l) (top:s) m pc | top == 0 = execInst (JUMP l) s m pc
>                                 | otherwise = (s,m,pc+1)
> execInst (LABEL l) s m pc = (s,m,pc+1)

Given a list of instructions (Code), we execute each in turn, checking to see whether the program counter has gone beyond the final instruction to indicate termination. The program counter is manipulated by the call to `execInst` in which it is simply incremented by 1 or, in the case of a jump instruction, is reassigned to the position of the given label. In this manner, `execCode` can cope with the jumping around because it recursively calls itself with the unaltered Code and thus always has access to every instruction and can freely index into the desired position using the program counter (using bang bang notation). The stack and memory are maintained and passed around throughout the entire process, as the execution of an instruction is fundamentally the manipulation of these structures (see `execInst` above).

> execCode :: Code -> Stack -> Mem -> Int -> (Stack,Mem)
> execCode c s m pc | pc >= (length c) = (s,m)
>                   | otherwise = execCode c s' m' pc'
>                                 where (s',m',pc') = execInst (c !! pc) s m pc

`execCode` is driven by `exec`, which initialises the memory with the label locations before starting and extracts the variables from memory after termination. The stack is initialised as empty. The (key,value) label locations do not interfere with standard memory variables because the key used by the labels is an integer converted to a character, whereas all programs will have their variable names as Chars (specifically, alphabetical symbols), so a clash is impossible. These pairs are then subtracted from the memory (using \\ imported from Data.List) upon termination so that the contents of it only contains the variables which were assigned during the execution.

> exec :: Code -> Mem
> exec c = snd (execCode c [] labels 0) \\ labels
>          where labels = storeLabels 0 c

An auxilliary function which operates on the memory: by treating Mem conceptually like a Map abstract datatype, we may implement the `put` operation to place a (key,value) pair into the datastructure by overwriting the existing key with the new value (second case of the second pattern), or, appending the pair to the datastructure if the key is new (first case of the second pattern). In our usage, the key is the variable Name which associates to its Int value, which we treat as the label value and associate to its position within the code, respsectively. The first pattern initialises the memory with its first label location.

> put :: (Name,Int) -> Mem -> Mem
> put (k,v) [] = [(k,v)]
> put (k,v) ((k',v'):ksvs) | k == k' = ((k,v):ksvs)
>                          | otherwise = (k',v'):(put (k,v) ksvs)

An auxilliary function which operates on the memory: we process all the code to find instructions which serve as labels and place them in the memory, using their Int value as the variable Name (== Char) in Mem to look up their associated Int value, which corresponds to their indexed location in the code. A simple recursive definition scans through the entire code and matches on all labels to place them in the memory one-at-a-time, building up the memory and eating up the code. The second pattern matches on the LABEL instruction and updates the memory and the third pattern just ignores any non-LABEL instruction as these are handled during execution.

> storeLabels :: Int -> Code -> Mem
> storeLabels p [] = []
> storeLabels p ((LABEL l):c) = ((intToDigit l),p):(storeLabels (p+1) c)
> storeLabels p (_:c) = storeLabels (p+1) c

Converts the given operator into the corresponing Haskell primitive. We restrict ourselves to integers, particularly for division, because the stack is only compatible with integers.

> operator :: Integral a => Op -> (a -> a -> a)
> operator Add = (+)
> operator Sub = (-)
> operator Mul = (*)
> operator Div = (div)

[END OF EXECUTION SECTION]

Test expression

> expr1 :: Expr
> expr1 = (App Mul (App Add (Val 1) (Val 2)) (App Add (Val 3) (Val 4)))

The factorial program

> fac :: Int -> Prog
> fac n = Seqn [Assign 'A' (Val 1),
>               Assign 'B' (Val n),
>               While (Var 'B') (Seqn
>                  [Assign 'A' (App Mul (Var 'A') (Var 'B')),
>                   Assign 'B' (App Sub (Var 'B') (Val (1)))])]
