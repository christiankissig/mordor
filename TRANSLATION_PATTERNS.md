# JavaScript to OCaml Translation Patterns

Guide to understanding the translation patterns used in converting the sMRD JavaScript codebase to OCaml.

## Type Conversions

### Primitives

```javascript
// JavaScript
let x = 42;
let s = "hello";
let b = true;
```

```ocaml
(* OCaml *)
let x = 42
let s = "hello"
let b = true
```

### BigInt to Zarith

```javascript
// JavaScript
const n = 42n;
const sum = a + b;
```

```ocaml
(* OCaml *)
let n = Z.of_int 42
let sum = Z.add a b
```

### undefined/null to option

```javascript
// JavaScript
let x = undefined;
if (x !== undefined) { ... }
```

```ocaml
(* OCaml *)
let x = None
match x with
| Some v -> ...
| None -> ...
```

## Data Structures

### Objects to Records

```javascript
// JavaScript
const event = {
  type: 'READ',
  id: 'x',
  value: 42n
};
```

```ocaml
(* OCaml *)
type event = {
  typ: event_type;
  id: string option;
  value: Z.t option;
}

let event = {
  typ = Read;
  id = Some "x";
  value = Some (Z.of_int 42);
}
```

### Maps/Objects to Hash Tables

```javascript
// JavaScript
const map = {};
map[key] = value;
const v = map[key];
```

```ocaml
(* OCaml *)
let map = Hashtbl.create 16
Hashtbl.add map key value
let v = Hashtbl.find map key
(* Or with option: *)
let v = try Some (Hashtbl.find map key) with Not_found -> None
```

### Arrays to Lists

```javascript
// JavaScript
const arr = [1, 2, 3];
arr.push(4);
arr.map(x => x * 2);
```

```ocaml
(* OCaml *)
let arr = [1; 2; 3]
let arr' = arr @ [4]
let doubled = List.map (fun x -> x * 2) arr
```

### Sets

```javascript
// JavaScript (custom USet)
const s = new USet();
s.add(x);
s.has(x);
s.union(other);
```

```ocaml
(* OCaml *)
let s = USet.create ()
USet.add s x
USet.mem s x
USet.union s other
```

## Classes to Modules

### JavaScript Class

```javascript
// JavaScript
class Event {
  constructor(type, id) {
    this.type = type;
    this.id = id;
  }
  
  isRead() {
    return this.type === 'READ';
  }
}

const e = new Event('READ', 'x');
```

### OCaml Module

```ocaml
(* OCaml *)
type event = {
  typ: event_type;
  id: string option;
}

module Event = struct
  let make typ id = { typ; id }
  
  let is_read e = e.typ = Read
end

let e = Event.make Read (Some "x")
```

## Async/Promises

### JavaScript Promises

```javascript
// JavaScript
async function foo() {
  const result = await bar();
  return result + 1;
}
```

### OCaml Lwt

```ocaml
(* OCaml *)
let foo () =
  let open Lwt.Syntax in
  let* result = bar () in
  Lwt.return (result + 1)

(* Or using infix: *)
let foo () =
  bar () >>= fun result ->
  Lwt.return (result + 1)
```

### Promise.all / Lwt_list

```javascript
// JavaScript
const results = await Promise.all(items.map(f));
```

```ocaml
(* OCaml *)
let* results = Lwt_list.map_p f items
```

### Async iteration

```javascript
// JavaScript
for (const item of items) {
  await process(item);
}
```

```ocaml
(* OCaml *)
let* () = Lwt_list.iter_s process items in
```

## Functions

### Arrow Functions

```javascript
// JavaScript
const double = x => x * 2;
const add = (a, b) => a + b;
```

```ocaml
(* OCaml *)
let double x = x * 2
let double = fun x -> x * 2

let add a b = a + b
let add = fun a b -> a + b
```

### Higher-Order Functions

```javascript
// JavaScript
array.map(x => x * 2)
     .filter(x => x > 10)
     .reduce((acc, x) => acc + x, 0);
```

```ocaml
(* OCaml *)
array
|> List.map (fun x -> x * 2)
|> List.filter (fun x -> x > 10)
|> List.fold_left (+) 0
```

### Optional Parameters

```javascript
// JavaScript
function foo(x, y = 42) { ... }
```

```ocaml
(* OCaml *)
let foo ?(y = 42) x = ...

(* Or: *)
let foo x y =
  let y = match y with Some v -> v | None -> 42 in
  ...
```

## Pattern Matching

### Switch to Match

```javascript
// JavaScript
switch (type) {
  case 'READ':
    return handleRead();
  case 'WRITE':
    return handleWrite();
  default:
    return null;
}
```

```ocaml
(* OCaml *)
match typ with
| Read -> handle_read ()
| Write -> handle_write ()
| _ -> None
```

### Destructuring

```javascript
// JavaScript
const [a, b] = pair;
const { x, y } = obj;
```

```ocaml
(* OCaml *)
let (a, b) = pair
let { x; y } = record
(* Or in match: *)
match pair with
| (a, b) -> ...
```

## Error Handling

### try/catch to Result/Option

```javascript
// JavaScript
try {
  const result = riskyOperation();
  return result;
} catch (e) {
  return null;
}
```

```ocaml
(* OCaml with option *)
let result =
  try Some (risky_operation ())
  with _ -> None

(* Or with Result: *)
let result =
  try Ok (risky_operation ())
  with e -> Error (Printexc.to_string e)
```

## Iteration

### for loops

```javascript
// JavaScript
for (let i = 0; i < n; i++) {
  process(i);
}
```

```ocaml
(* OCaml *)
for i = 0 to n - 1 do
  process i
done

(* Or functional: *)
List.init n process |> ignore
```

### while loops

```javascript
// JavaScript
while (condition) {
  doSomething();
}
```

```ocaml
(* OCaml *)
while condition do
  do_something ()
done

(* Or tail recursive: *)
let rec loop () =
  if condition then begin
    do_something ();
    loop ()
  end
in
loop ()
```

### Array.forEach

```javascript
// JavaScript
array.forEach(x => console.log(x));
```

```ocaml
(* OCaml *)
List.iter (fun x -> Printf.printf "%d\n" x) array
```

## Special Patterns

### Method Chaining to Pipe

```javascript
// JavaScript
obj.method1()
   .method2()
   .method3();
```

```ocaml
(* OCaml *)
obj
|> method1
|> method2
|> method3
```

### Getters/Setters to Functions

```javascript
// JavaScript
class Foo {
  get value() { return this._value; }
  set value(v) { this._value = v; }
}
```

```ocaml
(* OCaml *)
type foo = {
  mutable value: int;
}

let get_value f = f.value
let set_value f v = f.value <- v
```

### this to explicit parameters

```javascript
// JavaScript
class Foo {
  bar() {
    return this.x + this.y;
  }
}
```

```ocaml
(* OCaml *)
type foo = {
  x: int;
  y: int;
}

let bar self = self.x + self.y
```

## Memory Model Specific

### Event Representation

```javascript
// JavaScript
new Event(EventType.READ, {
  id: 'x',
  rval: Symbol('α'),
  rmod: Mode.ACQUIRE
})
```

```ocaml
(* OCaml *)
{
  typ = Read;
  id = Some (VVar "x");
  rval = Some (VSymbol "α");
  rmod = Acquire;
  (* ... other fields ... *)
}
```

### Relations (pairs)

```javascript
// JavaScript
const po = new USet([
  [0, 1],
  [1, 2]
]);
```

```ocaml
(* OCaml *)
let po = USet.of_list [
  (0, 1);
  (1, 2);
]
```

### Transitive Closure

```javascript
// JavaScript
const closure = rel.transitiveClosure();
```

```ocaml
(* OCaml *)
let closure = USet.transitive_closure rel
```

## Tips

1. **Naming**: JavaScript camelCase → OCaml snake_case
2. **Mutability**: Prefer immutable by default, use `mutable` when needed
3. **Errors**: Use `Result` or `option` instead of exceptions when possible
4. **Types**: Define types explicitly for clarity
5. **Modules**: Group related functionality
6. **Pattern matching**: Use extensively for clearer code
7. **Lwt**: Remember to use `let*` for async operations
8. **Hash tables**: Use for mutable maps, Map module for immutable

## Common Pitfalls

1. **Forgetting `let rec`** for recursive functions
2. **Missing semicolons** in imperative sequences
3. **Confusing `=` (equality) with `==` (physical equality)**
4. **Not handling `option` types properly**
5. **Forgetting `Lwt.return`** in async functions
6. **Using `List.append` in loops** (quadratic complexity)
7. **Not opening modules** (e.g., `Lwt.Syntax`)

## Example: Full Translation

### JavaScript

```javascript
class Solver {
  constructor(expressions) {
    this.exprs = expressions;
  }
  
  async solve() {
    for (const expr of this.exprs) {
      if (expr.isContradiction()) return false;
    }
    
    const result = await this.callZ3();
    return result;
  }
}
```

### OCaml

```ocaml
type solver = {
  exprs: expr list;
}

let create exprs = { exprs }

let solve solver =
  let open Lwt.Syntax in
  
  (* Check for contradictions *)
  let has_contradiction =
    List.exists Expr.is_contradiction solver.exprs
  in
  
  if has_contradiction then
    Lwt.return_false
  else
    let* result = call_z3 solver in
    Lwt.return result
```
