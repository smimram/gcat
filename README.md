# GCat

A graphical proof assistant for categories.

# Some notes

## Product as property

It might seem at first that having the rule

```
⊢ x : Obj, y : Obj
------------------
⊢ x×y : Obj
```

is a good idea but I don't think so in the end:

- being a product is a property rather than structure for an object (we don't
  want to have a particular choice) [for morphisms having structure is not that
  bad because we are up-to-equality in 1-categories]
- we cannot always take the product of two objects, so that we would need to
  condition the use of the above rule on a predicate `has-product(x,y)`
- we would like to have a rule which says that whenever we have an object `x×y`
  then we can construct an arrow `π₁ : x×y → x`, which means that π₁ depends on
  the fact that we have an object of the form x×y, and therefore does not take a
  context as argument (a context can only bind variables not patterns)
