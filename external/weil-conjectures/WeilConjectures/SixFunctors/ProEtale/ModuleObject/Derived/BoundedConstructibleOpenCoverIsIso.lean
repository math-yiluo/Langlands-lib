/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpaceEmbedding
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.TraceFormula.OpenCover

/-!
# Restrictions to a finite open cover detect isomorphisms in `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`

For finitely many open immersions `o i : U i ⟶ X` whose images cover a scheme `X` separated,
quasi-compact and locally of finite type over a field, a morphism `φ` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` whose
restrictions along every `o i` are isomorphisms is an isomorphism
(`ProEtale.CondensedRing.isIso_of_isIso_upperStar_of_isOpenImmersion`); in particular this holds
for the inclusions of finitely many opens covering `X`
(`ProEtale.CondensedRing.isIso_of_isIso_upperStar_overRestrictι`). This is the special case of
the detection along finite jointly surjective quasi-compact families
(`ProEtale.CondensedRing.isIso_of_forall_isIso_boundedConstructibleUpperStar_map`): an open
immersion into the noetherian scheme `X` is quasi-compact.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Finitely many open immersions covering `X` jointly reflect isomorphisms** of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧`: if the images of the open immersions `o i : U i ⟶ X` cover `X` and every
restriction `Lo_i^* φ` is an isomorphism, then `φ` is an isomorphism. -/
theorem isIso_of_isIso_upperStar_of_isOpenImmersion {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {ι : Type} [Finite ι] {U : ι → Over (Spec (.of k))} [∀ i, LocallyOfFiniteType (U i).hom]
    [∀ i, QuasiCompact (U i).hom] [∀ i, IsSeparated (U i).hom] (o : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (o i).left] (ho : ⋃ i, Set.range (o i).left.base = Set.univ)
    {A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : A ⟶ B)
    (h : ∀ i, IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (o i)).map φ)) :
    IsIso φ :=
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  isIso_of_forall_isIso_boundedConstructibleUpperStar_map _ ℓ o
    (fun x ↦ Set.mem_iUnion.1 (ho ▸ Set.mem_univ x)) φ h

/-- **Restrictions to a finite open cover jointly reflect isomorphisms** of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`: if
the opens `U i` cover `X` and every restriction `Lj_i^* φ` along `j_i : U i ⟶ X` is an
isomorphism, then `φ` is an isomorphism. -/
theorem isIso_of_isIso_upperStar_overRestrictι {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {ι : Type} [Finite ι] (U : ι → X.left.Opens) (hU : (⨆ i, U i) = ⊤)
    {A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (φ : A ⟶ B)
    (h : ∀ i, IsIso ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (overRestrictι X (U i))).map φ)) :
    IsIso φ :=
  isIso_of_isIso_upperStar_of_isOpenImmersion ℓ (fun i ↦ overRestrictι X (U i))
    (by simp_rw [range_overRestrictι, ← TopologicalSpace.Opens.coe_iSup, hU,
      TopologicalSpace.Opens.coe_top]) φ h

end AlgebraicGeometry.ProEtale.CondensedRing
