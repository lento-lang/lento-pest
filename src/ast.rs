// Abstract syntax tree for Lento.
//
// A `Program` is a vec of `Stmt`. Each `Stmt` is either a declaration or an
// expression. Expressions are an enum whose variants are small struct types.

/// A parsed Lento program: an ordered list of statements.
#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub statements: Vec<Stmt>,
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
    /// `spec name : spec_type` — a persistent local signature/contract.
    Spec(SpecDecl),
    /// `type name = type` — a named type synonym.
    Type(TypeDecl),
    /// `let [mut] pattern [: type] = expression` — binds an expression.
    Let(LetDecl),
}

/// `spec name : <spec_type>`
#[derive(Debug, Clone, PartialEq)]
pub struct SpecDecl {
    pub name: String,
    pub ty: SpecType,
}

/// `type name = <type>`
#[derive(Debug, Clone, PartialEq)]
pub struct TypeDecl {
    pub name: String,
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

/// Types. `mut`/`ref` are memory markers; functions are right-associative
/// arrows.
#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    Named { name: String, args: Vec<Ty> },
    Tuple(Vec<Ty>),
    List(Box<Ty>),
    #[allow(non_camel_case_types)]
    Arrow { from: Box<Ty>, to: Box<Ty> },
    Ref(Box<Ty>),
    Mut(Box<Ty>),
    NamedBinder { name: String, ty: Box<Ty> },
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
    /// `[a, b]` — list destructuring.
    List(Vec<Pattern>),
    /// `{ x: a, y: b }` — record destructuring.
    Record(Vec<RecordField>),
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
    Block(BlockExpr),
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
    Cons,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TupleExpr {
    pub items: Vec<Expr>,
}

/// A list is represented in the AST as nested cons cells, mirroring the
/// `::`/`[a]` structure. An empty list is `None`.
#[derive(Debug, Clone, PartialEq)]
pub enum ListExpr {
    Empty,
    Cells(Box<ListCons>),
}

/// `head :: tail`
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

/// Desugar a function clause `fn f p1 p2 ... pn = body` into a `let`
/// binding whose value is a curried chain of lambdas:
///
/// `let f = p1 => (p2 => (... (pn => body)))`.
///
/// Each parameter is a `Pattern` and becomes one lambda parameter; a
/// destructuring parameter (tuple/list/record) unpacks its argument.
pub fn desugar_fn(name: String, params: Vec<Pattern>, ret: Option<Ty>, body: Expr) -> LetDecl {
    let param_tys: Vec<Option<Ty>> = params.iter().map(param_type).collect();
    let mut value = body;
    for p in params.into_iter().rev() {
        value = Expr::Lambda(LambdaExpr {
            params: vec![p],
            body: Box::new(value),
        });
    }
    let annotation = match ret {
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
            kind: PatKind::Var(name.clone()),
        },
        annotation,
        value,
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
        // Literals, wildcards, lists and records do not carry recoverable
        // element types without more type inference.
        PatKind::Lit(_) | PatKind::Wildcard | PatKind::List(_) | PatKind::Record(_) => None,
    }
}
