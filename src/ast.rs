// Abstract syntax tree for Lento.
//
// A `Program` is a vec of `Stmt`. Each `Stmt` is either a declaration or an
// expression. Expressions are an enum whose variants are small struct types.

/// A parsed Lento program: an ordered list of statements.
///
/// `spans` holds one source position per statement (line, col, both 1-based),
/// aligned with `statements`. It is used by the type checker for error
/// locations; runtime lowering preserves the alignment.
#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub statements: Vec<Stmt>,
    pub spans: Vec<Span>,
}

/// A 1-based source position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub line: usize,
    pub col: usize,
}

/// A top-level statement: either a declaration or a bare expression.
#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Decl(Decl),
    Expr(Expr),
}

/// Declarations introduce bindings. Each is anchored by a keyword
/// (`spec`, `type`, `let`). `fn` has no AST node of its own: a function
/// clause is syntax sugar that desugars immediately into a `let` binding
/// whose value is a curried chain of lambdas.
#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    /// `class Name params* { spec ... }` — a named scope of required specs.
    Class(ClassDecl),
    /// `impl Class Target { fn ... }` — an explicit class implementation.
    Impl(ImplDecl),
    /// `spec name : spec_type` — a persistent local signature/contract.
    Spec(SpecDecl),
    /// `type name = type` — a named type synonym.
    Type(TypeDecl),
    /// `let [mut] pattern [: type] = expression` — binds an expression.
    Let(LetDecl),
    /// `fn name function_pattern* [-> type] = expression` — one clause of a
    /// function definition. Kept as its own node so `fn` source round-trips
    /// through the pretty printer (see the evaluator note below).
    Fn(FnDecl),
    /// `mod name { ... }` — an inline module.
    Mod(ModDecl),
    /// `use name.subname` — imports every declaration from a module directly.
    Use(UseDecl),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ModDecl {
    pub name: String,
    pub body: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct UseDecl {
    pub path: Vec<String>,
}

/// `class name params* { spec ... }`
#[derive(Debug, Clone, PartialEq)]
pub struct ClassDecl {
    pub name: String,
    pub params: Vec<String>,
    /// Kind annotation per parameter, parallel to `params` (`None` when
    /// written bare). A `None` parameter used at a higher kind in a spec
    /// body gets its kind inferred from usage.
    pub param_kinds: Vec<Option<Kind>>,
    pub specs: Vec<SpecDecl>,
}

/// `impl class target { fn ... }`
#[derive(Debug, Clone, PartialEq)]
pub struct ImplDecl {
    pub class: String,
    pub quantifiers: Vec<Quantifier>,
    pub target: Vec<Ty>,
    pub methods: Vec<FnDecl>,
}

/// `spec name : <spec_type>`
#[derive(Debug, Clone, PartialEq)]
pub struct SpecDecl {
    pub name: String,
    pub ty: SpecType,
}

/// `type name params* = <type>`
#[derive(Debug, Clone, PartialEq)]
pub struct TypeDecl {
    pub name: String,
    /// Type parameters bound on the left-hand side (`type Option a = ...`).
    pub params: Vec<String>,
    pub ty: Ty,
}

/// `let [mut] pattern [: type] = expression`
#[derive(Debug, Clone, PartialEq)]
pub struct LetDecl {
    pub mutable: bool,
    pub pattern: Pattern,
    pub annotation: Option<Ty>,
    pub value: Expr,
}

/// `fn name function_pattern* [-> type] = expression` — a single clause of a
/// function definition. `fn` is sugar over `let` + lambda + (for grouped
/// clauses) pattern matching: the evaluator desugars before interpreting, and
/// the pretty printer keeps the `fn` source form intact.
#[derive(Debug, Clone, PartialEq)]
pub struct FnDecl {
    pub name: String,
    pub params: Vec<Pattern>,
    pub ret: Option<Ty>,
    pub body: Expr,
}

/// A spec type: optional quantifiers, a function type, and an optional
/// `where` refinement.
#[derive(Debug, Clone, PartialEq)]
pub struct SpecType {
    pub quantifiers: Vec<Quantifier>,
    pub ty: Ty,
    pub where_: Option<Vec<Expr>>,
}

/// `all a b :: Ord, Show.`
#[derive(Debug, Clone, PartialEq)]
pub struct Quantifier {
    pub vars: Vec<String>,
    pub constraints: Vec<Constraint>,
}

/// `Ord` or `Ord T`
#[derive(Debug, Clone, PartialEq)]
pub struct Constraint {
    pub name: String,
    pub args: Vec<Ty>,
}

/// The kind of a type: `Star` is a proper type (kind `*`); `Arrow(a, b)` is
/// the kind of a type constructor taking `a` and yielding `b`, written
/// `a -> b` (right-associative).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    Star,
    Arrow(Box<Kind>, Box<Kind>),
}

impl Kind {
    /// The kind of a constructor applied to `applied` arguments when its full
    /// arity is `arity`: the remaining arrow. `None` when over-applied.
    pub fn applied(arity: usize, applied: usize) -> Option<Kind> {
        if applied > arity {
            return None;
        }
        let mut kind = Kind::Star;
        for _ in applied..arity {
            kind = Kind::Arrow(Box::new(Kind::Star), Box::new(kind));
        }
        Some(kind)
    }
}

impl std::fmt::Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Star => write!(f, "*"),
            Kind::Arrow(from, to) => {
                let needs_parens = matches!(**from, Kind::Arrow(_, _));
                if needs_parens {
                    write!(f, "({from}) -> {to}")
                } else {
                    write!(f, "{from} -> {to}")
                }
            }
        }
    }
}

/// Types. `mut`/`ref` are memory markers; functions are right-associative
/// arrows.
#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    Named {
        name: String,
        args: Vec<Ty>,
    },
    Tuple(Vec<Ty>),
    List(Box<Ty>),
    #[allow(non_camel_case_types)]
    Arrow {
        from: Box<Ty>,
        to: Box<Ty>,
    },
    Ref(Box<Ty>),
    Mut(Box<Ty>),
    NamedBinder {
        name: String,
        ty: Box<Ty>,
    },
    /// `int | str` or `Some a | None` — a sum type declaration body.
    Sum(Vec<SumAlt>),
    /// `{ a: int, b: bool }` — a record type.
    RecordType(Vec<(String, Ty)>),
    /// `{ a: int, ...rest }` — an open record type.
    OpenRecordType {
        fields: Vec<(String, Ty)>,
        row: String,
    },
}

/// One alternative of a sum type: an uppercase constructor with an optional
/// payload type (`Some a`, `None`) or a bare member type (`int`, `str`).
#[derive(Debug, Clone, PartialEq)]
pub enum SumAlt {
    Ctor {
        name: String,
        payload: Option<Ty>,
    },
    Bare(Ty),
    /// `...r` — an open row of additional alternatives.
    Row(String),
}

/// A left-value pattern: a shape that a value is matched or bound against.
/// Used for `let` bindings, function/lambda parameters, and (pending) match
/// arms. The pattern itself may carry an optional type annotation
/// (`(x : Int)`), and its destructuring parts (`Tuple`/`List`/`Record`) are
/// themselves `Pattern` nodes.
#[derive(Debug, Clone, PartialEq)]
pub struct Pattern {
    /// Optional type annotation on this pattern, e.g. `(x : Int)`.
    pub annotation: Option<Ty>,
    pub kind: PatKind,
}

/// The concrete shape of a pattern.
#[derive(Debug, Clone, PartialEq)]
pub enum PatKind {
    Var(String),
    Wildcard,
    Lit(Lit),
    /// `(a, b)` — tuple destructuring.
    Tuple(Vec<Pattern>),
    /// `[a, b]` or `[a, ...rest]` — list destructuring.
    List(Vec<Pattern>),
    /// `...rest` — spread/rest binder inside a list pattern, capturing the
    /// remaining suffix as a list.
    Spread(String),
    /// `{ x: a, y: b }` or `{ x: a, ...rest }` — record destructuring.
    Record {
        fields: Vec<RecordField>,
        rest: Option<String>,
    },
    /// `Some x` — an uppercase constructor pattern with a payload pattern.
    /// Bare uppercase names (`None`) are parsed as `Var` and resolved to
    /// constructor matches by the checker/evaluator.
    Constructor {
        name: String,
        payload: Option<Box<Pattern>>,
    },
}

/// One field of a record pattern `{ x: pat }`.
#[derive(Debug, Clone, PartialEq)]
pub struct RecordField {
    pub name: String,
    pub pattern: Pattern,
}

/// A literal pattern, mirroring expression literals.
#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    Bool(bool),
    Int(i64),
    Float(f64),
    Str(String),
}

/// Expressions are an enum; each variant is its own struct type.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Lit(LitExpr),
    Var(VarExpr),
    Ref(RefExpr),
    Assign(AssignExpr),
    Lambda(LambdaExpr),
    Call(CallExpr),
    Member(MemberExpr),
    Index(IndexExpr),
    Unary(UnaryExpr),
    Binary(BinaryExpr),
    Tuple(TupleExpr),
    List(ListExpr),
    Record(RecordValueExpr),
    Block(BlockExpr),
    Match(MatchExpr),
}

#[derive(Debug, Clone, PartialEq)]
pub struct LitExpr {
    pub value: Lit,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VarExpr {
    pub name: String,
}

/// `ref x` — materialize a borrow as a value.
#[derive(Debug, Clone, PartialEq)]
pub struct RefExpr {
    pub inner: Box<Expr>,
}

/// `place := value` mutation.
#[derive(Debug, Clone, PartialEq)]
pub struct AssignExpr {
    pub place: Box<Expr>,
    pub value: Box<Expr>,
}

/// `pattern[+] => body` — an anonymous function.
#[derive(Debug, Clone, PartialEq)]
pub struct LambdaExpr {
    pub params: Vec<Pattern>,
    pub body: Box<Expr>,
}

/// `f(args)`
#[derive(Debug, Clone, PartialEq)]
pub struct CallExpr {
    pub callee: Box<Expr>,
    pub args: Vec<Expr>,
}

/// `obj.field`
#[derive(Debug, Clone, PartialEq)]
pub struct MemberExpr {
    pub obj: Box<Expr>,
    pub field: String,
}

/// `obj[index]`
#[derive(Debug, Clone, PartialEq)]
pub struct IndexExpr {
    pub obj: Box<Expr>,
    pub index: Box<Expr>,
}

/// Prefix operators introducing a sub-expression (reserved).
#[derive(Debug, Clone, PartialEq)]
pub struct UnaryExpr {
    pub op: UnaryOp,
    pub operand: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinaryExpr {
    pub op: BinaryOp,
    pub lhs: Box<Expr>,
    pub rhs: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TupleExpr {
    pub items: Vec<Expr>,
}

/// A list is represented in the AST as nested cons cells, mirroring the
/// `[a]` syntax. An empty list is `None`. (Lists are extended at runtime with
/// the `concat` intrinsic; there is no cons operator.)
#[derive(Debug, Clone, PartialEq)]
pub enum ListExpr {
    Empty,
    Cells(Box<ListCons>),
    /// `...expr` — splice a list value's elements into the literal here.
    /// `rest` continues the literal spine after the spread.
    Spread {
        source: Box<Expr>,
        rest: Box<ListExpr>,
    },
}

/// `head :: tail` — one link of the list-literal spine.
#[derive(Debug, Clone, PartialEq)]
pub struct ListCons {
    pub head: Box<Expr>,
    pub tail: Box<ListExpr>,
}

/// `{ ... }` — a block of statements.
#[derive(Debug, Clone, PartialEq)]
pub struct BlockExpr {
    pub body: Vec<Stmt>,
}

/// `{ a: 1, ...r, b: 2 }` — a record value literal. Entries apply in order:
/// a spread merges another record's fields, a field inserts or overrides the
/// key. A bare `{}` is a block, never an empty record.
#[derive(Debug, Clone, PartialEq)]
pub struct RecordValueExpr {
    pub entries: Vec<RecordValueEntry>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RecordValueEntry {
    Field(String, Expr),
    Spread(Expr),
}

/// `match scrutinee { pattern [if guard] => body, ... }` — a pattern match.
#[derive(Debug, Clone, PartialEq)]
pub struct MatchExpr {
    pub scrutinee: Box<Expr>,
    pub arms: Vec<MatchArm>,
}

/// One arm of a `match`: a pattern (with optional guard) mapped to a body.
#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub pattern: Pattern,
    /// Optional guard expression, `if guard`, checked before the body.
    pub guard: Option<Expr>,
    pub body: Box<Expr>,
}

impl FnDecl {
    /// Desugar one function clause `fn f p1 p2 ... pn = body` into a `let`
    /// binding whose value is a curried chain of lambdas:
    ///
    /// `let f = p1 => (p2 => (... (pn => body)))`.
    ///
    /// Each parameter is a `Pattern` and becomes one lambda parameter; a
    /// destructuring parameter (tuple/list/record) unpacks its argument.
    pub fn desugar(self) -> LetDecl {
        let param_tys: Vec<Option<Ty>> = self.params.iter().map(param_type).collect();
        let mut value = self.body;
        for p in self.params.into_iter().rev() {
            value = Expr::Lambda(LambdaExpr {
                params: vec![p],
                body: Box::new(value),
            });
        }
        let annotation = match self.ret {
            Some(ret) if param_tys.iter().all(Option::is_some) => {
                let mut t = ret;
                for pt in param_tys.into_iter().rev().flatten() {
                    t = Ty::Arrow {
                        from: Box::new(pt),
                        to: Box::new(t),
                    };
                }
                Some(t)
            }
            _ => None,
        };
        LetDecl {
            mutable: false,
            pattern: Pattern {
                annotation: None,
                kind: PatKind::Var(self.name.clone()),
            },
            annotation,
            value,
        }
    }
}

/// Recover the (annotated) type of a pattern parameter, when known.
pub fn param_type(p: &Pattern) -> Option<Ty> {
    if let Some(t) = &p.annotation {
        return Some(t.clone());
    }
    match &p.kind {
        PatKind::Var(name) => Some(Ty::Named {
            name: name.clone(),
            args: Vec::new(),
        }),
        PatKind::Tuple(ps) => {
            let mut tys = Vec::with_capacity(ps.len());
            for p in ps {
                tys.push(param_type(p)?);
            }
            Some(Ty::Tuple(tys))
        }
        // Literals, wildcards, lists, spread, records and constructors do not
        // carry recoverable element types without more type inference.
        PatKind::Lit(_)
        | PatKind::Wildcard
        | PatKind::List(_)
        | PatKind::Spread(_)
        | PatKind::Record { .. }
        | PatKind::Constructor { .. } => None,
    }
}
