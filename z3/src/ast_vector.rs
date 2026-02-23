use crate::ast::Ast;
use crate::Context;
use z3_sys::*;

/// Vector of Z3 AST nodes.
/// 
/// Provides a container for managing collections of Z3 AST objects
/// with proper reference counting and memory management.
#[derive(Debug)]
pub struct AstVector {
    pub(crate) ctx: Context,
    pub(crate) z3_ast_vector: Z3_ast_vector,
}

impl Drop for AstVector {
    fn drop(&mut self) {
        unsafe {
            Z3_ast_vector_dec_ref(self.ctx.z3_ctx.0, self.z3_ast_vector);
        }
    }
}

impl AstVector {
    /// Create a new empty AST vector.
    pub fn new() -> AstVector {
        let ctx = Context::thread_local();
        unsafe {
            let av = Z3_mk_ast_vector(ctx.z3_ctx.0).unwrap();
            Z3_ast_vector_inc_ref(ctx.z3_ctx.0, av);
            AstVector {
                ctx: ctx.clone(),
                z3_ast_vector: av,
            }
        }
    }

    /// Wrap an existing Z3 AST vector.
    pub(crate) unsafe fn wrap(ctx: &Context, z3_ast_vector: Z3_ast_vector) -> AstVector {
        unsafe {
            Z3_ast_vector_inc_ref(ctx.z3_ctx.0, z3_ast_vector);
        }
        AstVector {
            ctx: ctx.clone(),
            z3_ast_vector,
        }
    }

    /// Get the number of elements in the vector.
    pub fn len(&self) -> usize {
        unsafe { Z3_ast_vector_size(self.ctx.z3_ctx.0, self.z3_ast_vector) as usize }
    }

    /// Check if the vector is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the element at the specified index.
    /// 
    /// # Panics
    /// Panics if the index is out of bounds.
    pub fn get(&self, index: usize) -> crate::ast::Dynamic {
        assert!(index < self.len(), "Index {} out of bounds", index);
        unsafe {
            crate::ast::Dynamic::wrap(
                &self.ctx,
                Z3_ast_vector_get(self.ctx.z3_ctx.0, self.z3_ast_vector, index as u32).unwrap(),
            )
        }
    }

    /// Set the element at the specified index.
    /// 
    /// # Panics
    /// Panics if the index is out of bounds.
    pub fn set(&self, index: usize, ast: &impl Ast) {
        assert!(index < self.len(), "Index {} out of bounds", index);
        unsafe {
            Z3_ast_vector_set(
                self.ctx.z3_ctx.0,
                self.z3_ast_vector,
                index as u32,
                ast.get_z3_ast(),
            );
        }
    }

    /// Push an element to the end of the vector.
    pub fn push(&self, ast: &impl Ast) {
        unsafe {
            Z3_ast_vector_push(self.ctx.z3_ctx.0, self.z3_ast_vector, ast.get_z3_ast());
        }
    }

    /// Resize the vector to the specified size.
    /// If the new size is larger, the new elements are uninitialized.
    pub fn resize(&self, new_size: usize) {
        unsafe {
            Z3_ast_vector_resize(self.ctx.z3_ctx.0, self.z3_ast_vector, new_size as u32);
        }
    }

    /// Convert the vector to a Rust Vec.
    pub fn to_vec(&self) -> Vec<crate::ast::Dynamic> {
        (0..self.len())
            .map(|i| self.get(i))
            .collect()
    }

    /// Create an AST vector from a slice of AST objects.
    pub fn from_slice<T: Ast>(asts: &[&T]) -> AstVector {
        let vector = AstVector::new();
        for ast in asts {
            vector.push(*ast);
        }
        vector
    }

    /// Translate the AST vector to another context.
    pub fn translate(&self, target_ctx: &Context) -> AstVector {
        unsafe {
            AstVector::wrap(
                target_ctx,
                Z3_ast_vector_translate(
                    self.ctx.z3_ctx.0,
                    self.z3_ast_vector,
                    target_ctx.z3_ctx.0,
                ).unwrap(),
            )
        }
    }

    /// Convert the vector to a string representation.
    pub fn to_string(&self) -> String {
        unsafe {
            let s = Z3_ast_vector_to_string(self.ctx.z3_ctx.0, self.z3_ast_vector);
            std::ffi::CStr::from_ptr(s).to_string_lossy().into_owned()
        }
    }
}

impl Default for AstVector {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Display for AstVector {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.to_string())
    }
}

/// Iterator over AST vector elements.
#[derive(Debug)]
pub struct AstVectorIter<'a> {
    vector: &'a AstVector,
    index: usize,
}

impl<'a> Iterator for AstVectorIter<'a> {
    type Item = crate::ast::Dynamic;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.vector.len() {
            let item = self.vector.get(self.index);
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }
}

impl<'a> IntoIterator for &'a AstVector {
    type Item = crate::ast::Dynamic;
    type IntoIter = AstVectorIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        AstVectorIter {
            vector: self,
            index: 0,
        }
    }
}