/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BaseChange.StalkTrace
public import WeilConjectures.TraceFormula.BaseChange.Supertrace
public import WeilConjectures.TraceFormula.ShriekTraceFunctionFiniteEtale

/-!

# The local traces of a Weil object and of its base change to `k̄`

Let `(K, φ)` be a Weil object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for an automorphism `e` of a scheme `X` over
the finite field `k`, and `x̄ : Spec k̄ ⟶ X` a geometric point with
`x̄ ≫ e^{n+1} = σ^{n+1} ≫ x̄`, `σ` the geometric Frobenius of `k̄`. The local trace
`t_{n+1}(K; x̄) = ∑ⱼ (-1)ʲ Tr(Fr_{x̄,n+1} | Hʲ(K)_x̄)` (`weilStalkTraceAlternatingSum`) is computed
on the base change `Lπ^* K` to `X ×_k k̄`, a Weil object for the model Frobenius
`Φ = (e^{n+1} ≫ F_X^{n+1}) ×_k k̄` (`weilGeometricBaseChange`): `x̄' = (x̄, 𝟙)` is fixed by `Φ`
and `t_{n+1}(K; x̄)` is the supertrace of the homology of the local Frobenius `F_{x̄'}` of the
iterate `(Lπ^* K, φ^{(n+1)})` at `x̄'`. By `proposition-properties-trace`, item (4), this supertrace
is the trace of `F_{x̄'}`.

## Main results

- `ProEtale.CondensedRing.weilSheafStalkTrace_homologyFunctor_eq`: the comparison in each degree.
- `ProEtale.CondensedRing.weilStalkTraceAlternatingSum_eq_superTrace`: `t_{n+1}(K; x̄)` is the
  supertrace of the homology of the model local Frobenius.
- `ProEtale.CondensedRing.homologyUnitEndRingHom_weilStalkTraceAlternatingSum`: `t_{n+1}(K; x̄)` is
  the
  trace of the model local Frobenius.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {e : X ≅ X} (n : ℕ)
  (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
  (hxk : x ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
  (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x)

instance instFactPrimeRingCharAlgebraicClosure_localTrace
    : Fact (ringChar (AlgebraicClosure k)).Prime :=
  ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ Fact.out⟩

instance instFactNeNatRingCharAlgebraicClosure_localTrace
    : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
  ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ Fact.out⟩

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
lemma WeilSheaf.frobeniusStalk_eq_powStalkFunctor_obj (F : WeilSheaf ℓ e) :
    WeilSheaf.frobeniusStalk ℓ (n + 1) x hx F = (WeilSheaf.powStalkFunctor ℓ (n + 1) x hx).obj F :=
  rfl

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
lemma WeilSheaf.frobeniusStalk_eq_stalkFunctor_obj_powFunctor_obj (F : WeilSheaf ℓ e) :
    WeilSheaf.frobeniusStalk ℓ (n + 1) x hx F = (WeilSheaf.stalkFunctor ℓ (e.pow (n + 1))
      ((geometricFrobeniusField k).pow (n + 1)).hom x hx).obj
        ((WeilSheaf.powFunctor ℓ e (n + 1)).obj F) :=
  (WeilSheaf.frobeniusStalk_eq_powStalkFunctor_obj ℓ n x hx F).trans
    ((congrArg (fun G ↦ G.obj F) (WeilSheaf.powStalkFunctor_eq_comp ℓ n x hx)).trans
      (Functor.comp_obj _ _ _))

/-- **The local trace of a Weil sheaf of homology in terms of the base change**, in each degree:
`Tr(Fr_{x̄,n+1} | Hʲ(K)_x̄) = Tr(Hʲ(F_{x̄'}) | Hʲ((Lπ^* K)_x̄'))`, where `F_{x̄'}` is the local
Frobenius at `x̄' = (x̄, 𝟙)` of the base change of the iterate `(K, φ^{(n+1)})`, for the model
Frobenius `(e^{n+1} ≫ F_X^{n+1}) ×_k k̄`. -/
theorem weilSheafStalkTrace_homologyFunctor_eq (K : WeilBoundedConstructible ℓ e.hom) (j : ℤ) :
    weilSheafStalkTrace ℓ (n + 1) x hx ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K) =
      traceOrZero ((DerivedCategory.homologyFunctor _ j).map
        ((weilStalk ℓ (baseChangeModelFrobenius (AlgebraicClosure k) X (n + 1) (e.pow (n + 1)).hom)
          (geometricBaseChangePoint x hxk)
          ((geometricBaseChangePoint_comp_modelFrobenius_eq_iff x hxk (n + 1) (e.pow (n + 1)).hom
            ((geometricFrobeniusField k).pow (n + 1)) (geometricFrobeniusField_pow_inv n)).2
              hx)).obj
          ((weilGeometricBaseChange (AlgebraicClosure k) ℓ X (n + 1) (e.pow (n + 1)).hom).obj
            (K.powSucc ℓ n))).frobenius.hom.hom) := by
  have h1 := IsoAlgebra.traceOrZero_str_congr ((WeilSheaf.stalkFunctor ℓ (e.pow (n + 1))
    ((geometricFrobeniusField k).pow (n + 1)).hom x hx).mapIso
      (WeilBoundedConstructible.homologyPowSuccIso ℓ n K j))
  have h2 := traceOrZero_stalkFunctor_homologyFunctor_eq_of_hom_eq ℓ (n + 1) (e.pow (n + 1))
    ((geometricFrobeniusField k).pow (n + 1)) (geometricFrobeniusField_pow_inv n) x hxk hx
    ((geometricFrobeniusField k).pow (n + 1)).hom rfl hx (K.powSucc ℓ n) j
  have t : weilSheafStalkTrace ℓ (n + 1) x hx ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj
      K) =
      traceOrZero (WeilSheaf.frobeniusStalk ℓ (n + 1) x hx
        ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K)).str.hom := rfl
  rw [WeilSheaf.frobeniusStalk_eq_stalkFunctor_obj_powFunctor_obj ℓ n x hx] at t
  exact t.trans (h1.symm.trans h2)

/-- **The local trace of a Weil object as a supertrace on its base change**: the local trace
`t_{n+1}(K; x̄) = ∑ⱼ (-1)ʲ Tr(Fr_{x̄,n+1} | Hʲ(K)_x̄)` is the supertrace
`∑ⱼ (-1)ʲ Tr(Hʲ(F_{x̄'}) | Hʲ((Lπ^* K)_x̄'))` of the homology of the local Frobenius `F_{x̄'}` at
`x̄' = (x̄, 𝟙)` of the base change `Lπ^* K` of the iterate `(K, φ^{(n+1)})`, a Weil object for the
model Frobenius `(e^{n+1} ≫ F_X^{n+1}) ×_k k̄`. -/
theorem weilStalkTraceAlternatingSum_eq_superTrace (K : WeilBoundedConstructible ℓ e.hom) :
    weilStalkTraceAlternatingSum ℓ (n + 1) x hx K =
      superTrace
        (fun j ↦ (DerivedCategory.homologyFunctor _ j).obj
          ((weilStalk ℓ (baseChangeModelFrobenius (AlgebraicClosure k) X (n + 1) (e.pow (n +
              1)).hom)
            (geometricBaseChangePoint x hxk)
            ((geometricBaseChangePoint_comp_modelFrobenius_eq_iff x hxk (n + 1)
              (e.pow (n + 1)).hom ((geometricFrobeniusField k).pow (n + 1))
                (geometricFrobeniusField_pow_inv n)).2 hx)).obj
            ((weilGeometricBaseChange (AlgebraicClosure k) ℓ X (n + 1) (e.pow (n + 1)).hom).obj
              (K.powSucc ℓ n))).carrier.obj)
        (fun j ↦ (DerivedCategory.homologyFunctor _ j).map
          ((weilStalk ℓ (baseChangeModelFrobenius (AlgebraicClosure k) X (n + 1) (e.pow (n +
              1)).hom)
            (geometricBaseChangePoint x hxk)
            ((geometricBaseChangePoint_comp_modelFrobenius_eq_iff x hxk (n + 1)
              (e.pow (n + 1)).hom ((geometricFrobeniusField k).pow (n + 1))
                (geometricFrobeniusField_pow_inv n)).2 hx)).obj
            ((weilGeometricBaseChange (AlgebraicClosure k) ℓ X (n + 1) (e.pow (n + 1)).hom).obj
              (K.powSucc ℓ n))).frobenius.hom.hom) :=
  finsum_congr fun j ↦ congrArg (fun t ↦ (j.negOnePow : ℤ) • t)
    (weilSheafStalkTrace_homologyFunctor_eq ℓ n x hxk hx K j)

attribute [local instance] boundedConstructibleBraiding in
/-- **The local trace of a Weil object as the trace of the model local Frobenius**: placed in
degree `0`, the local trace `t_{n+1}(K; x̄)` is the trace of the local Frobenius `F_{x̄'}` at
`x̄' = (x̄, 𝟙)` of the base change `Lπ^* K` of the iterate `(K, φ^{(n+1)})`, a Weil object for the
model Frobenius `(e^{n+1} ≫ F_X^{n+1}) ×_k k̄`, on the dualizable stalk `(Lπ^* K)_x̄'`
(blueprint `proposition-properties-trace`, item (4)). The dualizability of the stalk is a
hypothesis until the dualizability of stalks of objects of `Dᵇc` is available. -/
theorem homologyUnitEndRingHom_weilStalkTraceAlternatingSum (K : WeilBoundedConstructible ℓ e.hom)
    [HasRightDual
      ((weilStalk ℓ (baseChangeModelFrobenius (AlgebraicClosure k) X (n + 1) (e.pow (n + 1)).hom)
        (geometricBaseChangePoint x hxk)
        ((geometricBaseChangePoint_comp_modelFrobenius_eq_iff x hxk (n + 1)
          (e.pow (n + 1)).hom ((geometricFrobeniusField k).pow (n + 1))
            (geometricFrobeniusField_pow_inv n)).2 hx)).obj
        ((weilGeometricBaseChange (AlgebraicClosure k) ℓ X (n + 1) (e.pow (n + 1)).hom).obj
          (K.powSucc ℓ n))).carrier] :
    (homologyUnitEndRingHom ℓ (point (AlgebraicClosure k))
        (weilStalkTraceAlternatingSum ℓ (n + 1) x hx K)).asHom =
      trace ((weilStalk ℓ (baseChangeModelFrobenius (AlgebraicClosure k) X (n + 1) (e.pow (n +
          1)).hom)
        (geometricBaseChangePoint x hxk)
        ((geometricBaseChangePoint_comp_modelFrobenius_eq_iff x hxk (n + 1)
          (e.pow (n + 1)).hom ((geometricFrobeniusField k).pow (n + 1))
            (geometricFrobeniusField_pow_inv n)).2 hx)).obj
        ((weilGeometricBaseChange (AlgebraicClosure k) ℓ X (n + 1) (e.pow (n + 1)).hom).obj
          (K.powSucc ℓ n))).frobenius.hom := by
  rw [weilStalkTraceAlternatingSum_eq_superTrace ℓ n x hxk hx K]
  exact (trace_eq_homologyUnitEndRingHom_superTrace ℓ (AlgebraicClosure k) _ _).symm

end AlgebraicGeometry.ProEtale.CondensedRing
