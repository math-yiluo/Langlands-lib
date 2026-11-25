/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExceptionalHom
public import WeilConjectures.TraceFormula.KunnethVerdierTheorem

/-!

# The trace class of a cohomological correspondence

Let `c = (C, c₁, c₂, u)` be an endocorrespondence of `(X, K)`, with support map
`c = (c₁, c₂) : C ⟶ X ⨯ X`, fixed locus `ι : Fix(c) ⟶ C` and `d = ι ≫ c₁ : Fix(c) ⟶ X`, so that
the fixed square `ι ≫ c = d ≫ Δ_X` is cartesian (`Correspondence.FixedLocus.isPullback`). The
*trace class* of `u` is the Borel–Moore section (blueprint `definition-trace-class-local-terms--1`,
`definition-trace-class-local-terms`)
```
Tr_c(u) : ℚ̄_ℓ,Fix(c) ⟶ ω_Fix(c)
```
(`ProEtale.CondensedRing.Correspondence.traceClass`), the `Lι^* ⊣ Rι_*` adjoint of
```
ℚ̄_ℓ,C --ũ--> 𝓗_c(K) --𝔱--> Rι_* ω_Fix(c),
```
where
* `𝓗_c(K) = RHom(Lc₂^* K, Rc₁^! K)` is the *trace-class source* and `ũ` the mate of `u`
  (`Correspondence.traceClassSource`, `Correspondence.mate`, blueprint
  `lemma-external-duality-trace-morphism--2`);
* `𝔱` is the *trace morphism from external duality* (`Correspondence.traceMap`, blueprint
  `definition-trace-morphism--1`):
  ```
  𝓗_c(K) ≅ Rc^! (K ⊠ D_X K) --Rc^! e_K--> Rc^! RΔ_* ω_X ≅ Rι_* Rd^! ω_X ≅ Rι_* ω_Fix(c),
  ```
  the external duality isomorphism (`Correspondence.verdierDualityIso`, blueprint
  `lemma-external-duality-trace-morphism`: the exceptional internal hom exchange
  `RHom(Lc^* M, Rc^! N) ≅ Rc^! RHom(M, N)` of blueprint
  `lemma-external-duality-trace-morphism--2` followed by the inverse Künneth–Verdier map), the
  evaluation kernel `e_K : K ⊠ D_X K ⟶ RΔ_* ω_X` adjoint to the evaluation
  `K ⊗ D_X K ⟶ ω_X` (`evaluationKernel`), the right-adjoint form of compact-support base change
  in the fixed square (`Correspondence.FixedLocus.upperShriekLowerStarIso`, blueprint
  `definition-trace-morphism--1`) and the composition isomorphism `Rd^! ω_X ≅ ω_Fix(c)` of
  the dualizing complexes.

The construction uses the derived projection formula (blueprint `thm-sf-pf-proetale`), compact
support base change and the Künneth–Verdier theorem (blueprint
`lemma-external-duality-trace-morphism--1`) only through the invertibility of the canonical maps; it
needs no further hypothesis on `c` or `K` (blueprint `definition-trace-class-local-terms--1`).

## Main statements

- `ProEtale.CondensedRing.Correspondence.integral_traceClass_ofEnd`: over the base point,
  `∫_s Tr(v) = tr(v)`.

The Lefschetz–Verdier formula
(`ProEtale.CondensedRing.Correspondence.trace_globalOperator_eq_integral_traceClass`) is in
`WeilConjectures.TraceFormula.LefschetzVerdier`, and the local term of the Frobenius
correspondence at a fixed point
(`ProEtale.CondensedRing.WeilBoundedConstructible.localTerm_traceClass_graph_eq_trace`) is in
`WeilConjectures.TraceFormula.FrobeniusLocalTerm`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))}

/-! ### Evaluation kernels -/

section Evaluation

variable (ℓ) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The identification `LΔ_X^* (K ⊠ N) ≅ K ⊗ N` of the restriction of an external product to the
diagonal: the monoidal structure of `LΔ_X^*` and `L(Δ_X ≫ p_i)^* = L(𝟙)^* ≅ 𝟭`. -/
noncomputable def diagUpperStarExternalProductIso
    (K N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ (diag X)).obj (externalProduct ℓ K N) ≅ K ⊗ N :=
  (Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ (diag X)) _ _).symm ≪≫
    tensorIso
      (((boundedConstructibleUpperStarComp _ ℓ (diag X) prod.fst).app K).symm ≪≫
        eqToIso (by rw [diag, prod.lift_fst]) ≪≫
        (boundedConstructibleUpperStarId _ ℓ X).app K)
      (((boundedConstructibleUpperStarComp _ ℓ (diag X) prod.snd).app N).symm ≪≫
        eqToIso (by rw [diag, prod.lift_snd]) ≪≫
        (boundedConstructibleUpperStarId _ ℓ X).app N)

/-- The *evaluation kernel* `e_K : K ⊠ D_X K ⟶ RΔ_* ω_X` (blueprint
`definition-trace-morphism--1`, `theorem-proper-pushforward-lefschetz-verdier--1`): the
`LΔ^* ⊣ RΔ_*` adjoint of the evaluation `LΔ^* (K ⊠ D_X K) ≅ K ⊗ D_X K ⟶ ω_X`. -/
noncomputable def evaluationKernel (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ K (verdierDual ℓ K) ⟶
      (boundedConstructibleLowerStar ℓ (diag X)).obj (dualizingComplex' ℓ X) :=
  (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X)).homEquiv _ _
    ((diagUpperStarExternalProductIso ℓ K _).hom ≫ (ihom.ev K).app (dualizingComplex' ℓ X))

end Evaluation

/-! ### The class of a correspondence -/

section CorrespondenceClass

variable (ℓ) {C Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom] (c : C ⟶ Y ⨯ X)

/-- **The class of a correspondence** (blueprint `lemma-external-duality-trace-morphism--2`): for
the support `c = (c₁, c₂) : C ⟶ Z = Y ⨯ X` of a correspondence from `(X, K)` to `(Y, L)`, with
`c₁ = c ≫ p₁` and `c₂ = c ≫ p₂`, the tensor–hom adjunction, the derived projection formula for
`c` and the exceptional adjunction give a bijection
```
Hom(Rc_! ℚ̄_ℓ,C, RHom(Lp₂^* K, Rp₁^! L)) ≃ Hom(Lc₂^* K, Rc₁^! L),
```
natural in `K` and `L` (`correspondenceClassEquiv_naturality_left`,
`correspondenceClassEquiv_naturality_right`). The *class* `[u]` of a coefficient map `u` is its
inverse image, a class supported on `c`. -/
noncomputable def correspondenceClassEquiv (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerShriek ℓ c).obj (𝟙_ _) ⟶
        (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj K)).obj
          ((boundedConstructibleUpperShriek ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj L)) ≃
      ((boundedConstructibleUpperStar _ ℓ (c ≫ prod.snd)).obj K ⟶
        (boundedConstructibleUpperShriek ℓ (c ≫ prod.fst)).obj L) where
  toFun g := (boundedConstructibleUpperStarComp _ ℓ c prod.snd).hom.app K ≫
    Verdier.correspondenceClassEquiv (boundedConstructibleUpperShriekAdjunction ℓ c)
      (boundedConstructibleExceptionalProjection ℓ c) _ _ g ≫
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ c prod.fst).inv.app L
  invFun f := (Verdier.correspondenceClassEquiv (boundedConstructibleUpperShriekAdjunction ℓ c)
      (boundedConstructibleExceptionalProjection ℓ c) _ _).symm
    ((boundedConstructibleUpperStarComp _ ℓ c prod.snd).inv.app K ≫ f ≫
      (boundedConstructibleUpperShriekComp_padicAlgCl ℓ c prod.fst).hom.app L)
  left_inv g := by
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id,
      Iso.inv_hom_id_app_assoc, Equiv.symm_apply_apply]
  right_inv f := by
    simp only [Equiv.apply_symm_apply, Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id, Iso.hom_inv_id_app_assoc]

lemma correspondenceClassEquiv_apply (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (g : (boundedConstructibleLowerShriek ℓ c).obj (𝟙_ _) ⟶
        (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj K)).obj
          ((boundedConstructibleUpperShriek ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj L)) :
    correspondenceClassEquiv ℓ c K L g =
      (boundedConstructibleUpperStarComp _ ℓ c prod.snd).hom.app K ≫
        Verdier.correspondenceClassEquiv (boundedConstructibleUpperShriekAdjunction ℓ c)
          (boundedConstructibleExceptionalProjection ℓ c) _ _ g ≫
        (boundedConstructibleUpperShriekComp_padicAlgCl ℓ c prod.fst).inv.app L :=
  rfl

/-- Naturality of the class bijection in `L` (blueprint
`lemma-external-duality-trace-morphism--2`). -/
lemma correspondenceClassEquiv_naturality_right
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {L L' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (b : L ⟶ L')
    (g : (boundedConstructibleLowerShriek ℓ c).obj (𝟙_ _) ⟶
        (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj K)).obj
          ((boundedConstructibleUpperShriek ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj L)) :
    correspondenceClassEquiv ℓ c K L'
        (g ≫ (ihom _).map ((boundedConstructibleUpperShriek ℓ prod.fst).map b)) =
      correspondenceClassEquiv ℓ c K L g ≫
        (boundedConstructibleUpperShriek ℓ (c ≫ prod.fst)).map b := by
  exact Verdier.correspondenceClassEquiv_naturality_right_conj
    (boundedConstructibleUpperShriekAdjunction ℓ c)
    (boundedConstructibleExceptionalProjection ℓ c) _
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ c prod.fst)
    ((boundedConstructibleUpperStarComp _ ℓ c prod.snd).hom.app K) b g

/-- Naturality of the class bijection in `K` (blueprint
`lemma-external-duality-trace-morphism--2`). -/
lemma correspondenceClassEquiv_naturality_left
    {K K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (a : K' ⟶ K)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (g : (boundedConstructibleLowerShriek ℓ c).obj (𝟙_ _) ⟶
        (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj K)).obj
          ((boundedConstructibleUpperShriek ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj L)) :
    correspondenceClassEquiv ℓ c K' L
        (g ≫ (pre ((boundedConstructibleUpperStar _ ℓ prod.snd).map a)).app _) =
      (boundedConstructibleUpperStar _ ℓ (c ≫ prod.snd)).map a ≫
        correspondenceClassEquiv ℓ c K L g := by
  exact Verdier.correspondenceClassEquiv_naturality_left_conj
    (boundedConstructibleUpperShriekAdjunction ℓ c)
    (boundedConstructibleExceptionalProjection ℓ c) _
    (boundedConstructibleUpperStarComp _ ℓ c prod.snd)
    ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ c prod.fst).inv.app L) a g

end CorrespondenceClass

/-! ### The trace class -/

namespace Correspondence

section

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)

/-- The *trace-class source* `𝓗_c(K) = RHom(Lc₂^* K, Rc₁^! K)` of an endocorrespondence
(blueprint `lemma-external-duality-trace-morphism--2`). -/
noncomputable def traceClassSource : Dᵇc(c.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (ihom ((boundedConstructibleUpperStar _ ℓ c.c₂).obj K)).obj
    ((boundedConstructibleUpperShriek ℓ c.c₁).obj K)

/-- The *mate* `ũ : ℚ̄_ℓ,C ⟶ 𝓗_c(K)` of the coefficient map `u`, its transpose under the
tensor–hom adjunction (blueprint `lemma-external-duality-trace-morphism--2`). -/
noncomputable def mate : 𝟙_ _ ⟶ c.traceClassSource :=
  curry' c.u

/-- The mate construction identifies coefficient maps `Lc₂^* K ⟶ Rc₁^! K` with sections of the
trace-class source (blueprint `lemma-external-duality-trace-morphism--2`). -/
noncomputable def mateEquiv :
    ((boundedConstructibleUpperStar _ ℓ c.c₂).obj K ⟶
        (boundedConstructibleUpperShriek ℓ c.c₁).obj K) ≃
      (𝟙_ _ ⟶ c.traceClassSource) :=
  curryHomEquiv'

lemma mateEquiv_apply_u : c.mateEquiv c.u = c.mate :=
  rfl

/-- The **exceptional internal hom exchange** for the support map (blueprint
`lemma-external-duality-trace-morphism--2`): for `M, N` on `X ⨯ X`,
`RHom(Lc^* M, Rc^! N) ≅ Rc^! RHom(M, N)`, built from the derived projection formula for `c`
and the two adjunctions. -/
noncomputable def exceptionalHomIso (M N : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (ihom ((boundedConstructibleUpperStar _ ℓ c.support).obj M)).obj
        ((boundedConstructibleUpperShriek ℓ c.support).obj N) ≅
      (boundedConstructibleUpperShriek ℓ c.support).obj ((ihom M).obj N) :=
  haveI := Verdier.isIso_exceptionalHomMap_of_isIso
    (boundedConstructibleUpperShriekAdjunction ℓ c.support)
    (boundedConstructibleExceptionalProjection ℓ c.support) M N
  asIso (Verdier.exceptionalHomMap (boundedConstructibleUpperShriekAdjunction ℓ c.support)
    (boundedConstructibleExceptionalProjection ℓ c.support) M N)

/-- The trace-class source in terms of the support map:
`RHom(Lc₂^* K, Rc₁^! K) ≅ RHom(Lc^* Lp₂^* K, Rc^! Rp₁^! K)`, by the composition isomorphisms
for `c₂ = c ≫ p₂` and `c₁ = c ≫ p₁`. -/
noncomputable def traceClassSourceIso :
    c.traceClassSource ≅
      (ihom ((boundedConstructibleUpperStar _ ℓ c.support).obj
          ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj K))).obj
        ((boundedConstructibleUpperShriek ℓ c.support).obj
          ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ X ⟶ X)).obj K)) :=
  ihomIsoOfIso
    (eqToIso (by rw [support_snd]) ≪≫
      (boundedConstructibleUpperStarComp _ ℓ c.support prod.snd).app K)
    (eqToIso (by rw [support_fst]) ≪≫
      (boundedConstructibleUpperShriekComp_padicAlgCl ℓ c.support prod.fst).app K)

/-- The **external duality isomorphism** of the trace-class source (blueprint
`lemma-external-duality-trace-morphism`): `𝓗_c(K) ≅ Rc^! (K ⊠ D_X K)`, the exceptional internal hom
exchange `RHom(Lc^* Lp₂^* K, Rc^! Rp₁^! K) ≅ Rc^! RHom(Lp₂^* K, Rp₁^! K)` followed by `Rc^!` of the
inverse Künneth–Verdier isomorphism `κ_{K,K}`. -/
noncomputable def verdierDualityIso :
    c.traceClassSource ≅
      (boundedConstructibleUpperShriek ℓ c.support).obj
        (externalProduct ℓ K (verdierDual ℓ K)) :=
  c.traceClassSourceIso ≪≫ c.exceptionalHomIso _ _ ≪≫
    (boundedConstructibleUpperShriek ℓ c.support).mapIso
      (asIso (kunnethVerdierMap ℓ K K)).symm

namespace FixedLocus

variable {c} (F : c.FixedLocus)

/-- **Base change in the fixed square** (blueprint `definition-trace-morphism--1`, (2)):
compact-support base change `LΔ_X^* Rc_! ≅ Rd_! Lι^*` in the cartesian fixed square. -/
noncomputable def lowerShriekBaseChangeIso :
    boundedConstructibleLowerShriek ℓ c.support ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (diag X) ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι ⋙
        boundedConstructibleLowerShriek ℓ F.d :=
  haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ F.isPullback
  asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ F.isPullback)

/-- **Base change in the fixed square, right-adjoint form** (blueprint
`definition-trace-morphism--1`, (2)): `Rc^! RΔ_{X*} ≅ Rι_* Rd^!`, the conjugate of
`lowerShriekBaseChangeIso` for the composite adjunctions `Rc_! ⋙ LΔ^* ⊣ RΔ_* ⋙ Rc^!` and
`Lι^* ⋙ Rd_! ⊣ Rd^! ⋙ Rι_*`. -/
noncomputable def upperShriekLowerStarIso :
    boundedConstructibleLowerStar ℓ (diag X) ⋙
        boundedConstructibleUpperShriek ℓ c.support ≅
      boundedConstructibleUpperShriek ℓ F.d ⋙
        boundedConstructibleLowerStar ℓ F.ι :=
  conjugateIsoEquiv
    ((boundedConstructibleUpperShriekAdjunction ℓ c.support).comp
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X)))
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι).comp
      (boundedConstructibleUpperShriekAdjunction ℓ F.d))
    F.lowerShriekBaseChangeIso.symm

/-- **Pullback along the ordinary leg in the fixed square** (blueprint
`definition-trace-morphism--1`, (1)): `Lι^* Lc₂^* K ≅ Ld^* K`, from `ι ≫ c₂ = d`. -/
noncomputable def upperStarC₂Iso (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ F.ι).obj ((boundedConstructibleUpperStar _ ℓ c.c₂).obj K) ≅
      (boundedConstructibleUpperStar _ ℓ F.d).obj K :=
  ((boundedConstructibleUpperStarComp _ ℓ F.ι c.c₂).app K).symm ≪≫
    eqToIso (by rw [F.ι_c₂])

end FixedLocus

/-- The *trace morphism from external duality* `𝔱 : 𝓗_c(K) ⟶ Rι_* ω_Fix(c)` (blueprint
`definition-trace-morphism--1`, objectwise form):
```
𝓗_c(K) ≅ Rc^! (K ⊠ D_X K) --Rc^! e_K--> Rc^! RΔ_* ω_X ≅ Rι_* Rd^! ω_X ≅ Rι_* ω_Fix(c).
```
-/
noncomputable def traceMap (F : c.FixedLocus) :
    c.traceClassSource ⟶
      (boundedConstructibleLowerStar ℓ F.ι).obj (dualizingComplex' ℓ F.F) :=
  c.verdierDualityIso.hom ≫
    (boundedConstructibleUpperShriek ℓ c.support).map (evaluationKernel ℓ K) ≫
    (F.upperShriekLowerStarIso.app (dualizingComplex' ℓ X)).hom ≫
    (boundedConstructibleLowerStar ℓ F.ι).map (dualizingComplexComp ℓ F.d).hom

/-- The *trace class* `Tr_c(u) : ℚ̄_ℓ,Fix(c) ⟶ ω_Fix(c)` of an endocorrespondence (blueprint
`definition-trace-class-local-terms--1`, `definition-trace-class-local-terms`): the `Lι^* ⊣ Rι_*`
adjoint of the composite `ℚ̄_ℓ,C --ũ--> 𝓗_c(K) --𝔱--> Rι_* ω_Fix(c)` of the mate of `u` and the
trace morphism `traceMap`, read through `ℚ̄_ℓ,Fix(c) ≅ Lι^* ℚ̄_ℓ,C`. It is defined for every
correspondence, with no hypothesis beyond the finiteness conditions on the schemes (blueprint
`definition-trace-class-local-terms--1`). -/
noncomputable def traceClass (F : c.FixedLocus) : BorelMooreSection ℓ F.F :=
  (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ F.ι)).hom ≫
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι).homEquiv _ _).symm
      (c.mate ≫ c.traceMap F)

/-- **The trace class is unconditionally defined** (blueprint
`definition-trace-class-local-terms--1`): it is the image of the mate of `u` under the
`ℚ̄_ℓ`-linear map `Hom(ℚ̄_ℓ,C, 𝓗_c(K)) ⟶ Hom(ℚ̄_ℓ,Fix(c), ω_Fix(c))` induced by the trace
morphism, defined for every coefficient map `u`. -/
lemma traceClass_eq (F : c.FixedLocus) :
    c.traceClass F = (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ F.ι)).hom ≫
      ((boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι).homEquiv _ _).symm
        (c.mateEquiv c.u ≫ c.traceMap F) :=
  rfl

end

end Correspondence

namespace Correspondence

variable [QuasiCompact X.hom] [IsProper X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

instance (v : K ⟶ K) : IsProper (fixedLocusOfEnd v).F.hom :=
  inferInstanceAs (IsProper X.hom)

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
