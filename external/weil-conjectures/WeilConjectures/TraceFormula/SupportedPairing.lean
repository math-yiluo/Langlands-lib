/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.TraceClass

/-!

# The supported pairing of an opposite pair of correspondences

Let `X, Y` be separated `k`-schemes of finite type, `K ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, `L ∈ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`,
`Z = Y ⨯ X` with projections `p₁ : Z ⟶ Y`, `p₂ : Z ⟶ X`, and `τ : X ⨯ Y ≅ Y ⨯ X` the exchange
of the factors. An *opposite pair* consists of a correspondence from `(X, K)` to `(Y, L)`,
```
c : C ⟶ Z,   u : L(c ≫ p₂)^* K ⟶ R(c ≫ p₁)^! L,
```
and a correspondence from `(Y, L)` to `(X, K)`,
```
d : D ⟶ X ⨯ Y,   v : L(d ≫ q₂)^* L ⟶ R(d ≫ q₁)^! K,
```
together with the fibre product `E = C ×_{c, Z, d̄} D` of the supports, `d̄ = d ≫ τ`. The
*supported pairing* `⟨u, v⟩_LV : ℚ̄_ℓ,E ⟶ ω_E` (`ProEtale.CondensedRing.supportedPairing`,
blueprint `def-trf-supported-pairing`) is the exceptional adjoint, along `e : E ⟶ Z`, of
```
Re_! ℚ̄_ℓ,E ≅ Rc_! ℚ̄_ℓ,C ⊗ Rd̄_! ℚ̄_ℓ,D --uc ⊗ vc--> (L ⊠ D_X K) ⊗ (D_Y L ⊠ K)
  ⟶ ω_Y ⊠ ω_X ⟶ ω_Z,
```
read through `Re^! ω_Z ≅ ω_E`, where:

* `uc = κ_{L,K}⁻¹ ∘ [u]` and `vc` are the supported classes of `u` and `v`
  (`ProEtale.CondensedRing.supportedClass`, `ProEtale.CondensedRing.oppositeSupportedClass`),
  the class of `lemma-external-duality-trace-morphism--2` read through the inverse Künneth–Verdier
  map, the second one transported along `τ`;
* the first isomorphism `μ` is built from the composition of the lower shrieks, compact-support
  base change in the cartesian square of `E` and the projection formula for `c`
  (`ProEtale.CondensedRing.supportProductIso`);
* the contraction uses the monoidality of `Lp_i^*`, the two evaluations, and the exterior
  product `ω_Y ⊠ ω_X ⟶ ω_Z` (`ProEtale.CondensedRing.dualizingComplexExternalProduct`, the
  exceptional Künneth map of blueprint `proposition-exceptional-external-kunneth--1` for `a_Y` and
  `a_X`).

The *local term* of the pair along an open and closed subscheme `B` of `E` proper over `s` is the
local term of the supported pairing (`ProEtale.CondensedRing.localTermPair`, blueprint
`def-trf-local-term-pair`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The lower shriek along an isomorphism -/

section Iso

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
/-- For an isomorphism `e : X ≅ Y`, the square `e⁻¹ ≫ e = 𝟙 ≫ 𝟙` is cartesian. -/
lemma isPullback_inv_hom (e : X ≅ Y) : IsPullback e.inv (𝟙 Y) e.hom (𝟙 Y) :=
  IsPullback.of_vert_isIso ⟨by simp⟩

/-- For an isomorphism `e : X ≅ Y`, the lower shriek `Re_!` is the pullback `L(e⁻¹)^*`, by
compact-support base change in the cartesian square `e⁻¹ ≫ e = 𝟙 ≫ 𝟙`. -/
noncomputable def lowerShriekIsoUpperStarInv (e : X ≅ Y) :
    boundedConstructibleLowerShriek ℓ e.hom ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e.inv :=
  haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (isPullback_inv_hom e)
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleUpperStarId _ ℓ Y).symm ≪≫
    asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (isPullback_inv_hom e)) ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerShriekId ℓ Y) ≪≫ Functor.rightUnitor _

end Iso

/-! ### Supported classes -/

section Classes

variable {X Y C D : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
  [IsSeparated C.hom] [LocallyOfFiniteType D.hom] [QuasiCompact D.hom] [IsSeparated D.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

/-- The *supported class* `uc = κ_{L,K}⁻¹ ∘ [u] : Rc_! ℚ̄_ℓ,C ⟶ L ⊠ D_X K` of a correspondence
`u : L(c ≫ p₂)^* K ⟶ R(c ≫ p₁)^! L` from `(X, K)` to `(Y, L)` with support `c : C ⟶ Y ⨯ X`
(blueprint `def-trf-supported-pairing`, Step 1): the class `[u]` of
`lemma-external-duality-trace-morphism--2`, a class supported on `c` in the sense of
`def-trf-supported-class`, read through the inverse Künneth–Verdier isomorphism. -/
noncomputable def supportedClass (c : C ⟶ Y ⨯ X)
    (u : (boundedConstructibleUpperStar _ ℓ (c ≫ prod.snd)).obj K ⟶
      (boundedConstructibleUpperShriek ℓ (c ≫ prod.fst)).obj L) :
    (boundedConstructibleLowerShriek ℓ c).obj (𝟙_ _) ⟶
      externalProduct ℓ L (verdierDual ℓ K) :=
  (correspondenceClassEquiv ℓ c K L).symm u ≫ inv (kunnethVerdierMap ℓ L K)

variable (X Y) in
/-- The exchange of the factors of an external product along `τ : X ⨯ Y ≅ Y ⨯ X`:
`Rτ_! (K ⊠ N) ≅ L(τ⁻¹)^* (Lq₁^* K ⊗ Lq₂^* N) ≅ Lp₂^* K ⊗ Lp₁^* N ≅ N ⊠ K`. -/
noncomputable def externalProductBraidingIso (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ (prod.braiding X Y).hom).obj (externalProduct ℓ K N) ≅
      externalProduct ℓ N K :=
  (lowerShriekIsoUpperStarInv ℓ (prod.braiding X Y)).app _ ≪≫
    (Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ (prod.braiding X Y).inv) _ _).symm ≪≫
    tensorIso
      (((boundedConstructibleUpperStarComp _ ℓ (prod.braiding X Y).inv prod.fst).app K).symm ≪≫
        eqToIso (by simp))
      (((boundedConstructibleUpperStarComp _ ℓ (prod.braiding X Y).inv prod.snd).app N).symm ≪≫
        eqToIso (by simp)) ≪≫
    β_ _ _

/-- The *supported class of the opposite correspondence* `vc : Rd̄_! ℚ̄_ℓ,D ⟶ D_Y L ⊠ K` on
`Y ⨯ X`, `d̄ = d ≫ τ` (blueprint `def-trf-supported-pairing`, Step 1): the supported class
`κ_{K,L}⁻¹ ∘ [v] : Rd_! ℚ̄_ℓ,D ⟶ K ⊠ D_Y L` on `X ⨯ Y`, transported along `Rd̄_! ≅ Rτ_! Rd_!`
and the exchange of the factors `Rτ_! (K ⊠ D_Y L) ≅ D_Y L ⊠ K`. -/
noncomputable def oppositeSupportedClass (d : D ⟶ X ⨯ Y)
    (v : (boundedConstructibleUpperStar _ ℓ (d ≫ prod.snd)).obj L ⟶
      (boundedConstructibleUpperShriek ℓ (d ≫ prod.fst)).obj K) :
    (boundedConstructibleLowerShriek ℓ (d ≫ (prod.braiding X Y).hom)).obj (𝟙_ _) ⟶
      externalProduct ℓ (verdierDual ℓ L) K :=
  (boundedConstructibleLowerShriekComp_padicAlgCl ℓ d (prod.braiding X Y).hom).hom.app _ ≫
    (boundedConstructibleLowerShriek ℓ (prod.braiding X Y).hom).map (supportedClass ℓ d v) ≫
    (externalProductBraidingIso ℓ X Y K _).hom

end Classes

/-! ### The exterior product of dualizing complexes -/

section Exterior

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

variable (X Y) in
/-- The *exterior product of the dualizing complexes* `ω_Y ⊠ ω_X ⟶ ω_{Y ⨯ X}`: the exceptional
adjoint of
```
Ra_Z! (ω_Y ⊠ ω_X) ≅ Ra_Y! Rp₁! (ω_Y ⊠ ω_X) ⟶ Ra_Y! ω_Y ⟶ ℚ̄_ℓ,s,
```
the composition isomorphism for `a_Z = p₁ ≫ a_Y`, the morphism `exceptionalKunnethAdjoint`
(projection formula, base change in the product square and the counit of `a_X`) and the counit
of `a_Y`. It is the exceptional Künneth map `α` of blueprint
`proposition-exceptional-external-kunneth--1` (`lemma-external-duality-trace-morphism`, (ii)) for
`f₁ = a_Y`, `f₂ = a_X`, `L₁ = L₂ = ℚ̄_ℓ`. -/
noncomputable def dualizingComplexExternalProduct :
    externalProduct ℓ (dualizingComplex' ℓ Y) (dualizingComplex' ℓ X) ⟶
      dualizingComplex' ℓ (Y ⨯ X) :=
  (boundedConstructibleUpperShriekAdjunction ℓ (toPoint (Y ⨯ X))).homEquiv _ _
    (eqToHom (by rw [← comp_toPoint (prod.fst : Y ⨯ X ⟶ Y)]) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (prod.fst : Y ⨯ X ⟶ Y)
        (toPoint Y)).hom.app _ ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Y)).map
        (exceptionalKunnethAdjoint ℓ (dualizingComplex' ℓ Y)) ≫
      (boundedConstructibleUpperShriekAdjunction ℓ (toPoint Y)).counit.app (𝟙_ _))

end Exterior

/-! ### The supported pairing -/

section Pairing

variable {X Y C D E : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
  [IsSeparated C.hom] [LocallyOfFiniteType D.hom] [QuasiCompact D.hom] [IsSeparated D.hom]
  [LocallyOfFiniteType E.hom] [QuasiCompact E.hom] [IsSeparated E.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : C ⟶ Y ⨯ X} {d' : D ⟶ Y ⨯ X} {eC : E ⟶ C} {eD : E ⟶ D}

/-- The *support of the product* (blueprint `def-trf-supported-pairing`, Step 2): for the
cartesian square `E = C ×_{c, Z, d'} D`,
```
R(eC ≫ c)_! ℚ̄_ℓ,E ≅ Rc_! ReC_! LeD^* ℚ̄_ℓ,D ≅ Rc_! (Lc^* Rd'_! ℚ̄_ℓ,D)
  ≅ Rc_! (ℚ̄_ℓ,C ⊗ Lc^* Rd'_! ℚ̄_ℓ,D) ≅ Rc_! ℚ̄_ℓ,C ⊗ Rd'_! ℚ̄_ℓ,D,
```
the composition of the lower shrieks, compact-support base change and the projection formula
for `c`. -/
noncomputable def supportProductIso (hE : IsPullback eC eD c d') :
    (boundedConstructibleLowerShriek ℓ (eC ≫ c)).obj (𝟙_ _) ≅
      (boundedConstructibleLowerShriek ℓ c).obj (𝟙_ _) ⊗
        (boundedConstructibleLowerShriek ℓ d').obj (𝟙_ _) :=
  haveI := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hE.flip
  (boundedConstructibleLowerShriekComp_padicAlgCl ℓ eC c).app _ ≪≫
    (boundedConstructibleLowerShriek ℓ c).mapIso
      ((boundedConstructibleLowerShriek ℓ eC).mapIso
          (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ eD)) ≪≫
        ((asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hE.flip)).app _).symm ≪≫
        (λ_ ((boundedConstructibleUpperStar _ ℓ c).obj
          ((boundedConstructibleLowerShriek ℓ d').obj (𝟙_ _)))).symm) ≪≫
    (asIso (((boundedConstructibleExceptionalProjection ℓ c).app (𝟙_ _)).app _)).symm

variable (L K) in
/-- The *contraction* of the kernels (blueprint `def-trf-supported-pairing`, Step 3):
```
(L ⊠ D_X K) ⊗ (D_Y L ⊠ K) ≅ (Lp₁^* L ⊗ Lp₁^* D_Y L) ⊗ (Lp₂^* K ⊗ Lp₂^* D_X K)
  ⟶ Lp₁^* (L ⊗ D_Y L) ⊗ Lp₂^* (K ⊗ D_X K) ⟶ ω_Y ⊠ ω_X ⟶ ω_Z,
```
the symmetry constraints, the monoidal structure of the pullbacks, the evaluations and the
exterior product of the dualizing complexes. -/
noncomputable def kernelContraction :
    externalProduct ℓ L (verdierDual ℓ K) ⊗
        externalProduct ℓ (verdierDual ℓ L) K ⟶
      dualizingComplex' ℓ (Y ⨯ X) :=
  (tensorTensorRearrangeIso _ _ _ _).hom ≫
    ((β_ _ _).hom ▷ _) ≫
    ((Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ X ⟶ Y)) _ _ ≫
        (boundedConstructibleUpperStar _ ℓ (prod.fst : Y ⨯ X ⟶ Y)).map
          ((ihom.ev L).app (dualizingComplex' ℓ Y))) ⊗ₘ
      ((β_ _ _).hom ≫
        Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)) _ _ ≫
        (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).map
          ((ihom.ev K).app (dualizingComplex' ℓ X)))) ≫
    dualizingComplexExternalProduct ℓ X Y

variable (c d') in
/-- The morphism `σ_{u,v} : R(eC ≫ c)_! ℚ̄_ℓ,E ⟶ ω_Z` of the supported pairing (blueprint
`def-trf-supported-pairing`, Step 3), for supported classes `uc : Rc_! ℚ̄_ℓ,C ⟶ L ⊠ D_X K` and
`vc : Rd'_! ℚ̄_ℓ,D ⟶ D_Y L ⊠ K`. -/
noncomputable def pairingMorphism (hE : IsPullback eC eD c d')
    (uc : (boundedConstructibleLowerShriek ℓ c).obj (𝟙_ _) ⟶
      externalProduct ℓ L (verdierDual ℓ K))
    (vc : (boundedConstructibleLowerShriek ℓ d').obj (𝟙_ _) ⟶
      externalProduct ℓ (verdierDual ℓ L) K) :
    (boundedConstructibleLowerShriek ℓ (eC ≫ c)).obj (𝟙_ _) ⟶
      dualizingComplex' ℓ (Y ⨯ X) :=
  (supportProductIso ℓ hE).hom ≫ (uc ⊗ₘ vc) ≫ kernelContraction ℓ K L

variable (c d') in
/-- The Borel–Moore section of `E` attached to supported classes `uc`, `vc` over the cartesian
square `E = C ×_Z D`: the exceptional adjoint, along `e = eC ≫ c : E ⟶ Z`, of the pairing
morphism, read through `Re^! ω_Z ≅ ω_E`. -/
noncomputable def pairingOfClasses (hE : IsPullback eC eD c d')
    (uc : (boundedConstructibleLowerShriek ℓ c).obj (𝟙_ _) ⟶
      externalProduct ℓ L (verdierDual ℓ K))
    (vc : (boundedConstructibleLowerShriek ℓ d').obj (𝟙_ _) ⟶
      externalProduct ℓ (verdierDual ℓ L) K) :
    BorelMooreSection ℓ E :=
  (boundedConstructibleUpperShriekAdjunction ℓ (eC ≫ c)).homEquiv _ _
      (pairingMorphism ℓ c d' hE uc vc) ≫
    (dualizingComplexComp ℓ (eC ≫ c)).hom

/-- The **supported pairing** `⟨u, v⟩_LV : ℚ̄_ℓ,E ⟶ ω_E` of an opposite pair (blueprint
`def-trf-supported-pairing`, `sk-d-pairing`, `rem-ptr-trf-supported-pairing-1`): for a
correspondence `u` from `(X, K)` to `(Y, L)` with support
`c : C ⟶ Y ⨯ X`, a correspondence `v` from `(Y, L)` to `(X, K)` with support `d : D ⟶ X ⨯ Y`
and the cartesian square `E = C ×_{c, Y ⨯ X, d ≫ τ} D`, the Borel–Moore section
`pairingOfClasses` of the supported classes `uc = supportedClass u` and
`vc = oppositeSupportedClass v`. -/
noncomputable def supportedPairing {d : D ⟶ X ⨯ Y}
    (u : (boundedConstructibleUpperStar _ ℓ (c ≫ prod.snd)).obj K ⟶
      (boundedConstructibleUpperShriek ℓ (c ≫ prod.fst)).obj L)
    (v : (boundedConstructibleUpperStar _ ℓ (d ≫ prod.snd)).obj L ⟶
      (boundedConstructibleUpperShriek ℓ (d ≫ prod.fst)).obj K)
    (hE : IsPullback eC eD c (d ≫ (prod.braiding X Y).hom)) : BorelMooreSection ℓ E :=
  pairingOfClasses ℓ c _ hE (supportedClass ℓ c u) (oppositeSupportedClass ℓ d v)

/-- The *local term of an opposite pair* along an open and closed subscheme `j : B ⟶ E` proper
over `s` (blueprint `def-trf-local-term-pair`): the local term `LT_B(u, v) = ∫_B j^* ⟨u, v⟩_LV`
of the supported pairing; the ambient `E` need not be proper. -/
noncomputable def localTermPair {d : D ⟶ X ⨯ Y}
    (u : (boundedConstructibleUpperStar _ ℓ (c ≫ prod.snd)).obj K ⟶
      (boundedConstructibleUpperShriek ℓ (c ≫ prod.fst)).obj L)
    (v : (boundedConstructibleUpperStar _ ℓ (d ≫ prod.snd)).obj L ⟶
      (boundedConstructibleUpperShriek ℓ (d ≫ prod.fst)).obj K)
    (hE : IsPullback eC eD c (d ≫ (prod.braiding X Y).hom)) {B : Over (Spec (.of k))}
    [QuasiCompact B.hom] [IsProper B.hom]
    (j : B ⟶ E) [IsOpenImmersion j.left] [IsClosedImmersion j.left] :
    End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :=
  (supportedPairing ℓ u v hE).localTerm j

end Pairing

end AlgebraicGeometry.ProEtale.CondensedRing
