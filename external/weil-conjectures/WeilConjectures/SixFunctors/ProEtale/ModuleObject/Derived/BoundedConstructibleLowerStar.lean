/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStarDeligne
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStarOfIsProper
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!

# The derived lower shriek and the derived hom on bounded constructible complexes

This file continues `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
(same setting, notation and namespaces), after the derived pushforward
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStarDeligne`
(Deligne's finiteness theorem, every morphism) and its proper-only version
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStarOfIsProper`,
for each of the three `ℓ`-adic coefficient rings `ℚ̲̄_ℓ`, `E̲` and `𝒪̲_E`:

* the derived lower shriek `Rf_!^c := i_! ⋙ Rp_*` for a compactification `c`
  (`boundedConstructibleLowerShriekOfCompactification`) and `Rf_!` for the compactification
  `compactificationOverField f` (`boundedConstructibleLowerShriek`), with their compatibilities
  with the derived lower shrieks on the ambient derived categories. The proper leg `Rp_*` is the
  proper-only functor `boundedConstructibleLowerStarOfIsProper`, which rests on the proper
  finiteness theorem and not on Deligne's finiteness theorem for arbitrary `f`;
* the monoidal closed structure on `Dᵇc(X)⟦Λ⟧`: `isMonoidalClosed_boundedConstructible`
  (`Dᵇc(X)⟦Λ⟧` is stable under `RHom(-, -)`, by noetherian induction from the lisse case,
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom`, using
  `boundedConstructible_rightDerivedLowerStar_obj` for open immersions), `boundedConstructibleHom`,
  `boundedConstructibleHomObjCompatibility` and the tensor-hom adjunctions
  `boundedConstructibleTensorHomAdjunction₂`, `boundedConstructibleTensorHomAdjunction`.

The file keeps its name so that its importers see the whole package (the two files above are
public imports).

-/

-- The `privateModule` linter alone takes about 20 s on `BoundedConstructible`.
set_option linter.privateModule false

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]


/-! ### The derived lower shriek -/

section Shriek

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` on bounded
constructible complexes attached to a compactification `c = (X.left ⟶[i] Z ⟶[p] Y.left)` of
`f.left`: the extension by zero along the open immersion `i` followed by the
derived pushforward along the proper morphism `p` (the proper-only functor
`boundedConstructibleLowerStarOfIsProper`), both on bounded constructible
complexes, for `i` and `p` the morphisms `c.overI` and `c.overG` of `Over (Spec (.of k))`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ c.overI ⋙
    boundedConstructibleLowerStarOfIsProper ℓ c.overG

/-- `Rf_!^c` on bounded constructible complexes is the restriction of the derived lower shriek
`Rf_!(c)⟦ℚ̲̄_ℓ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationCompatibility :
    boundedConstructibleLowerShriekOfCompactification ℓ c ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ Rf_!(c)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarOfIsProperCompatibility ℓ c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ
        c.overI) _ ≪≫
    Functor.associator _ _ _

end OfCompactification

variable (f : X ⟶ Y)

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` on bounded constructible
complexes: the functor `boundedConstructibleLowerShriekOfCompactification`
attached to the compactification `compactificationOverField f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleLowerShriekOfCompactification ℓ (compactificationOverField f)

/-- The defining equation of `boundedConstructibleLowerShriek` (`ℚ̄_ℓ`-coefficient). -/
lemma boundedConstructibleLowerShriek_eq :
    boundedConstructibleLowerShriek ℓ f =
      boundedConstructibleLowerShriekOfCompactification ℓ (compactificationOverField f) :=
  rfl

/-- The derived lower shriek on bounded constructible complexes is the restriction of the
derived lower shriek `R(f)_!⟦ℚ̲̄_ℓ⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    haveI := HasCompactification.of_over f
    boundedConstructibleLowerShriek ℓ f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f.left)_!⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ
    (compactificationOverField f)

end Shriek

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj


section Shriek

include ℓ k

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` on bounded
constructible complexes attached to a compactification `c = (X.left ⟶[i] Z ⟶[p] Y.left)` of
`f.left`: the extension by zero along the open immersion `i` followed by the
derived pushforward along the proper morphism `p` (the proper-only functor
`boundedConstructibleLowerStarOfIsProper`), both on bounded constructible
complexes, for `i` and `p` the morphisms `c.overI` and `c.overG` of `Over (Spec (.of k))`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧ :=
  boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ c.overI ⋙
    boundedConstructibleLowerStarOfIsProper ℓ E c.overG

/-- `Rf_!^c` on bounded constructible complexes is the restriction of the derived lower shriek
`Rf_!(c)⟦E̲⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationCompatibility :
    boundedConstructibleLowerShriekOfCompactification ℓ E c ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ Rf_!(c)⟦Profinite.continuousMapRingObj E⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarOfIsProperCompatibility ℓ E c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekCompatibility (Profinite.continuousMapRingObj E)
        ℓ
        c.overI) _ ≪≫
    Functor.associator _ _ _

end OfCompactification

variable (f : X ⟶ Y)

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` on bounded constructible
complexes: the functor `boundedConstructibleLowerShriekOfCompactification`
attached to the compactification `compactificationOverField f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧ :=
  boundedConstructibleLowerShriekOfCompactification ℓ E (compactificationOverField f)

/-- The defining equation of `boundedConstructibleLowerShriek` (`E`-coefficient). -/
lemma boundedConstructibleLowerShriek_eq :
    boundedConstructibleLowerShriek ℓ E f =
      boundedConstructibleLowerShriekOfCompactification ℓ E (compactificationOverField f) :=
  rfl

/-- The derived lower shriek on bounded constructible complexes is the restriction of the
derived lower shriek `R(f)_!⟦E̲⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    haveI := HasCompactification.of_over f
    boundedConstructibleLowerShriek ℓ E f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f.left)_!⟦Profinite.continuousMapRingObj E⟧ :=
  boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ E
    (compactificationOverField f)

end Shriek

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj


section Shriek

include ℓ k

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f.left)

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_* : Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` on bounded
constructible complexes attached to a compactification `c = (X.left ⟶[i] Z ⟶[p] Y.left)` of
`f.left`: the extension by zero along the open immersion `i` followed by the
derived pushforward along the proper morphism `p` (the proper-only functor
`boundedConstructibleLowerStarOfIsProper`), both on bounded constructible
complexes, for `i` and `p` the morphisms `c.overI` and `c.overG` of `Over (Spec (.of k))`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactification :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ
      E⟧ :=
  boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ c.overI ⋙
    boundedConstructibleLowerStarOfIsProper ℓ E c.overG

/-- `Rf_!^c` on bounded constructible complexes is the restriction of the derived lower shriek
`Rf_!(c)⟦𝒪̲_E⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationCompatibility :
    boundedConstructibleLowerShriekOfCompactification ℓ E c ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ Rf_!(c)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarOfIsProperCompatibility ℓ E c.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekCompatibility
        (Profinite.padicIntegersRingObj ℓ E) ℓ
        c.overI) _ ≪≫
    Functor.associator _ _ _

end OfCompactification

variable (f : X ⟶ Y)

/-- The derived lower shriek `Rf_! : Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` on bounded constructible
complexes: the functor `boundedConstructibleLowerShriekOfCompactification`
attached to the compactification `compactificationOverField f` chosen by Nagata's theorem. -/
noncomputable def boundedConstructibleLowerShriek :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ
      E⟧ :=
  boundedConstructibleLowerShriekOfCompactification ℓ E (compactificationOverField f)

/-- The defining equation of `boundedConstructibleLowerShriek` (`𝒪_E`-coefficient). -/
lemma boundedConstructibleLowerShriek_eq :
    boundedConstructibleLowerShriek ℓ E f =
      boundedConstructibleLowerShriekOfCompactification ℓ E (compactificationOverField f) :=
  rfl

/-- The derived lower shriek on bounded constructible complexes is the restriction of the
derived lower shriek `R(f)_!⟦𝒪̲_E⟧` on the ambient derived categories. -/
noncomputable def boundedConstructibleLowerShriekCompatibility :
    haveI := HasCompactification.of_over f
    boundedConstructibleLowerShriek ℓ E f ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R(f.left)_!⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ E
    (compactificationOverField f)

end Shriek

end PadicIntegersRingObj

/-! ### The monoidal closed structure: the derived hom (needs
`boundedConstructible_rightDerivedLowerStar_obj`) -/

section TensorHom

include ℓ k

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

-- An instance keeps only the section variables its statement and proof mention, so its
-- hypotheses are restated as binders; they repeat section variables.
set_option linter.overlappingInstances false in
/-- Blueprint `proposition-six-operations-dctf--15`: the bounded constructible complexes of
`ℚ̄_ℓ`-sheaves are stable under the derived hom
`RHom(-, -)`, the internal hom of `D(Mod_{ℚ̄_ℓ,X})` (SGA 4½ [Th. finitude],
1.6; Bhatt–Scholze, Section 6.8). It is false for a general condensed ring: for `Λ = ℤ/4` on a
geometric point of characteristic `3`, `Ext^i_{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
theorem isMonoidalClosed_boundedConstructible :
    (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)).IsMonoidalClosed :=
  ⟨fun _ _ hK hL ↦ boundedConstructible_ihom_of_over
    (tensorHypotheses_padicAlgClRingObj ℓ).lisseHypotheses X
    (fun _ _ _ _ _ _ _ _ j _ A hA ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ j ⟨A, hA⟩)
    hK hL⟩
set_option linter.overlappingInstances false in
attribute [instance] isMonoidalClosed_boundedConstructible

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ᵒᵖ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X)⟦ℚ̲̄_ℓ⟧` on bounded
constructible complexes: the internal hom of the monoidal closed structure on
the full subcategory `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` (`ObjectProperty.fullMonoidalClosedSubcategory`), the
restriction of `RHom(X)⟦ℚ̲̄_ℓ⟧` in both variables. -/
noncomputable def boundedConstructibleHom :
    (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)ᵒᵖ ⥤ Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  MonoidalClosed.internalHom

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleHom ℓ X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧).obj (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- The adjunction with a parameter `- ⊗ᴸ - ⊣₂ RHom(-, -)` on bounded constructible complexes:
the tensor-hom adjunction of the monoidal closed structure on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`.
-/
noncomputable def boundedConstructibleTensorHomAdjunction₂ :
    boundedConstructibleTensor ℓ X ⊣₂ boundedConstructibleHom ℓ X :=
  MonoidalClosed.internalHomAdjunction₂

/-- For a fixed `K ∈ Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the tensor-hom adjunction `ihom.adjunction K` of the monoidal closed
structure on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleTensor ℓ X).obj K ⊣ (boundedConstructibleHom ℓ X).obj (op K) :=
  (boundedConstructibleTensorHomAdjunction₂ ℓ).adj K


end TensorHom

namespace ContinuousMapRingObj

section TensorHom

include ℓ k

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

-- An instance keeps only the section variables its statement and proof mention, so its
-- hypotheses are restated as binders; they repeat section variables.
set_option linter.overlappingInstances false in
/-- The bounded constructible complexes of `E`-sheaves are stable under the derived hom
`RHom(-, -)`, the internal hom of `D(Mod_{E_X})` (SGA 4½ [Th. finitude], 1.6;
Bhatt–Scholze, Section 6.8). It is false for a general condensed ring: for `Λ = ℤ/4` on a geometric
point of characteristic `3`, `Ext^i_{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
theorem isMonoidalClosed_boundedConstructible :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left)).IsMonoidalClosed :=
  ⟨fun _ _ hK hL ↦ boundedConstructible_ihom_of_over
    (tensorHypotheses_continuousMapRingObj ℓ E).lisseHypotheses X
    (fun _ _ _ _ _ _ _ _ j _ A hA ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ E j ⟨A, hA⟩)
    hK hL⟩
set_option linter.overlappingInstances false in
attribute [instance] isMonoidalClosed_boundedConstructible

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦E̲⟧ᵒᵖ ⥤ Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(X)⟦E̲⟧` on bounded
constructible complexes: the internal hom of the monoidal closed structure on the
full subcategory `Dᵇc(X)⟦E̲⟧` (`ObjectProperty.fullMonoidalClosedSubcategory`), the restriction
of `RHom(X)⟦E̲⟧` in both variables. -/
noncomputable def boundedConstructibleHom :
    (Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧)ᵒᵖ ⥤
      Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤
        Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ :=
  MonoidalClosed.internalHom

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦E̲⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleHom ℓ E X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X.left)⟦Profinite.continuousMapRingObj E⟧).obj
        (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- The adjunction with a parameter `- ⊗ᴸ - ⊣₂ RHom(-, -)` on bounded constructible complexes:
the tensor-hom adjunction of the monoidal closed structure on `Dᵇc(X)⟦E̲⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction₂ :
    boundedConstructibleTensor ℓ E X ⊣₂ boundedConstructibleHom ℓ E X :=
  MonoidalClosed.internalHomAdjunction₂

/-- For a fixed `K ∈ Dᵇc(X)⟦E̲⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the tensor-hom adjunction `ihom.adjunction K` of the monoidal closed
structure on `Dᵇc(X)⟦E̲⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    (boundedConstructibleTensor ℓ E X).obj K ⊣ (boundedConstructibleHom ℓ E X).obj (op K) :=
  (boundedConstructibleTensorHomAdjunction₂ ℓ E).adj K


end TensorHom

end ContinuousMapRingObj

namespace PadicIntegersRingObj

section TensorHom

include ℓ k

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

-- An instance keeps only the section variables its statement and proof mention, so its
-- hypotheses are restated as binders; they repeat section variables.
set_option linter.overlappingInstances false in
/-- The bounded constructible complexes of `𝒪_E`-sheaves are stable under the derived hom
`RHom(-, -)`, the internal hom of `D(Mod_{𝒪_{E,X}})` (SGA 4½ [Th. finitude],
1.6; Bhatt–Scholze, Section 6.8). It is false for a general condensed ring: for `Λ = ℤ/4` on a
geometric point of characteristic `3`, `Ext^i_{ℤ/4}(ℤ/2, ℤ/2) = ℤ/2` for all `i ≥ 0`. -/
theorem isMonoidalClosed_boundedConstructible :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)).IsMonoidalClosed :=
  ⟨fun _ _ hK hL ↦ boundedConstructible_ihom_of_over (lisseHypotheses ℓ E) X
    (fun _ _ _ _ _ _ _ _ j _ A hA ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ E j ⟨A, hA⟩)
    hK hL⟩
set_option linter.overlappingInstances false in
attribute [instance] isMonoidalClosed_boundedConstructible

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦𝒪̲_E⟧ᵒᵖ ⥤ Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(X)⟦𝒪̲_E⟧` on bounded
constructible complexes: the internal hom of the monoidal closed structure on
the full subcategory `Dᵇc(X)⟦𝒪̲_E⟧` (`ObjectProperty.fullMonoidalClosedSubcategory`), the
restriction of `RHom(X)⟦𝒪̲_E⟧` in both variables. -/
noncomputable def boundedConstructibleHom :
    (Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧)ᵒᵖ ⥤ Dᵇc(X.left)⟦Profinite.padicIntegersRingObj
      ℓ E⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  MonoidalClosed.internalHom

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦𝒪̲_E⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (boundedConstructibleHom ℓ E X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧).obj
        (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- The adjunction with a parameter `- ⊗ᴸ - ⊣₂ RHom(-, -)` on bounded constructible complexes:
the tensor-hom adjunction of the monoidal closed structure on `Dᵇc(X)⟦𝒪̲_E⟧`.
-/
noncomputable def boundedConstructibleTensorHomAdjunction₂ :
    boundedConstructibleTensor ℓ E X ⊣₂ boundedConstructibleHom ℓ E X :=
  MonoidalClosed.internalHomAdjunction₂

/-- For a fixed `K ∈ Dᵇc(X)⟦𝒪̲_E⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the tensor-hom adjunction `ihom.adjunction K` of the monoidal closed
structure on `Dᵇc(X)⟦𝒪̲_E⟧`. -/
noncomputable def boundedConstructibleTensorHomAdjunction
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    (boundedConstructibleTensor ℓ E X).obj K ⊣ (boundedConstructibleHom ℓ E X).obj (op K) :=
  (boundedConstructibleTensorHomAdjunction₂ ℓ E).adj K


end TensorHom

end PadicIntegersRingObj

end AlgebraicGeometry.ProEtale.CondensedRing

