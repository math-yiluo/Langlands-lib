/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.SixFunctors.NearbyCycles.Exchange

/-!

# Exchange maps of nearby cycles on bounded constructible complexes

The specialization unit `σ : Λ ⟶ Ψ Λ` (`NearbyCyclesModel.unit`) and the pushforward exchange
`χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` (`NearbyCyclesModel.Hom.pushforwardExchange`) of the ambient nearby
cycles, restricted to bounded constructible complexes
(`NearbyCyclesModel.boundedConstructibleUnit`,
`NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
section Abstract

/-- A transformation `χ : Rf ⋙ ΨN ⟶ ΨM ⋙ Rf'` between functors preserving full subcategories,
restricted to the full subcategories: the components are `χ` itself. -/
noncomputable def liftExchange {DY DX DY' DX' : Type*} [Category DY] [Category DX]
    [Category DY'] [Category DX'] {PY : ObjectProperty DY} {PX : ObjectProperty DX}
    {PY' : ObjectProperty DY'} {PX' : ObjectProperty DX'} {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    {ΨN : DY ⥤ DY'} {ΨM : DX ⥤ DX'} (χ : Rf ⋙ ΨN ⟶ ΨM ⋙ Rf')
    (hR : ∀ Z : PX.FullSubcategory, PY ((PX.ι ⋙ Rf).obj Z))
    (hR' : ∀ Z : PX'.FullSubcategory, PY' ((PX'.ι ⋙ Rf').obj Z))
    (hN : ∀ Z : PY.FullSubcategory, PY' ((PY.ι ⋙ ΨN).obj Z))
    (hM : ∀ Z : PX.FullSubcategory, PX' ((PX.ι ⋙ ΨM).obj Z)) :
    PY.lift (PX.ι ⋙ Rf) hR ⋙ PY'.lift (PY.ι ⋙ ΨN) hN ⟶
      PX'.lift (PX.ι ⋙ ΨM) hM ⋙ PY'.lift (PX'.ι ⋙ Rf') hR' where
  app P := ObjectProperty.homMk (χ.app P.obj)
  naturality _ _ g := by
    ext
    exact χ.naturality g.hom

@[simp]
lemma liftExchange_app_hom {DY DX DY' DX' : Type*} [Category DY] [Category DX]
    [Category DY'] [Category DX'] {PY : ObjectProperty DY} {PX : ObjectProperty DX}
    {PY' : ObjectProperty DY'} {PX' : ObjectProperty DX'} {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    {ΨN : DY ⥤ DY'} {ΨM : DX ⥤ DX'} (χ : Rf ⋙ ΨN ⟶ ΨM ⋙ Rf')
    (hR : ∀ Z : PX.FullSubcategory, PY ((PX.ι ⋙ Rf).obj Z))
    (hR' : ∀ Z : PX'.FullSubcategory, PY' ((PX'.ι ⋙ Rf').obj Z))
    (hN : ∀ Z : PY.FullSubcategory, PY' ((PY.ι ⋙ ΨN).obj Z))
    (hM : ∀ Z : PX.FullSubcategory, PX' ((PX.ι ⋙ ΨM).obj Z)) (Z : PX.FullSubcategory) :
    ((liftExchange χ hR hR' hN hM).app Z).hom = χ.app Z.obj :=
  rfl



end Abstract

section Exchange

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- The specialization unit `σ : ℚ̲̄_ℓ ⟶ Ψ ℚ̲̄_ℓ` on bounded constructible complexes: the ambient
specialization unit `NearbyCyclesModel.unit`. -/
noncomputable def boundedConstructibleUnit
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) :
    𝟙_ (Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) ⟶
      (boundedConstructibleNearbyCycles hM).obj (𝟙_ _) :=
  ObjectProperty.homMk (M.unit (Profinite.padicAlgClRingObj ℓ))

namespace Hom

variable (φ : M.Hom N f.left f'.left)
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))

/-- The pushforward exchange `χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` on bounded constructible complexes: the
restriction of `NearbyCyclesModel.Hom.pushforwardExchange`. -/
noncomputable def boundedConstructiblePushforwardExchange :
    boundedConstructibleLowerStar ℓ f ⋙ boundedConstructibleNearbyCycles hN ⟶
      boundedConstructibleNearbyCycles hM ⋙ boundedConstructibleLowerStar ℓ f' :=
  liftExchange (φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)) _ _ _ _


end Hom

end Exchange

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
