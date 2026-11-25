/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

set_option linter.privateModule false

/-! # Tensor comparison for the algebraic inverse image

Source: Stacks Project, Modules on Sites, Tags 03D1--03D3, 03D7 and 03EL.
(auxiliary; not a blueprint node).

Transport the right-adjoint module operations, restrict the set adjunction to
linear and bilinear maps, and apply the sheaf tensor universal property.
All five site and coefficient universe parameters remain independent.
-/

@[expose] public section

universe u uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

namespace CochainGeometricConstruction

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

set_option backward.isDefEq.respectTransparency true
open GeometricConstruction

/-- The module right adjoint with its transported addition and scalar action. -/
private theorem right_module_construction
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] [PreservesFiniteLimits V] [L.Braided] [V.Braided]
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf K CommRingCat.{u})
    (eR : rset A ≅ L.obj (rset R))
    (ha : ringAdd A ≫ eR.hom = (eR.hom ⊗ₘ eR.hom) ≫
      Functor.LaxMonoidal.μ L _ _ ≫ L.map (ringAdd R))
    (hm : ringMul A ≫ eR.hom = (eR.hom ⊗ₘ eR.hom) ≫
      Functor.LaxMonoidal.μ L _ _ ≫ L.map (ringMul R)) :
    ∃ (P : SheafOfModules.{u} (base A) ⥤ SheafOfModules.{u} (base R))
      (eP : P ⋙ mset R ≅ mset A ⋙ V),
      ∀ H : SheafOfModules.{u} (base A),
        (fromProd _ _ ≫ addition R (P.obj H)) ≫ eP.hom.app H =
          prod.map (eP.hom.app H) (eP.hom.app H) ≫
            inv (prodComparison V ((mset A).obj H) ((mset A).obj H)) ≫
              V.map (fromProd _ _ ≫ addition A H) ∧
        (fromProd _ _ ≫ action R (P.obj H)) ≫ eP.hom.app H =
          prod.map (adj.homEquiv _ _ eR.inv) (eP.hom.app H) ≫
            inv (prodComparison V (rset A) ((mset A).obj H)) ≫
              V.map (fromProd _ _ ≫ action A H) := by
  let : PreservesLimits V := adj.rightAdjoint_preservesLimits
  let d := adj.homEquiv (rset R) (rset A) eR.inv
  have haP : ringAdd R ≫ d = (d ⊗ₘ d) ≫ Functor.LaxMonoidal.μ V _ _ ≫
      V.map (ringAdd A) := by
    apply adjunct_binary L V adj _ _ _ _ eR.inv
    exact binary_inverse L _ _ eR _ _ ha
  have hmI := ringIso_isMonHom L R A eR hm
  have hmP : let := ringMonoid A
             let := ringMonoid R
             let := V.monObjObj (rset A)
             IsMonHom d := by
    let := ringMonoid R
    let := ringMonoid A
    let := L.monObjObj (rset R)
    let : IsMonHom eR.hom := hmI
    let := V.monObjObj (rset A)
    refine ⟨?_, ?_⟩
    · apply adjunct_constant L V adj _ _ (ringOne R) (ringOne A) eR.inv
      apply (cancel_epi (Functor.LaxMonoidal.ε L)).1
      have hu : (Functor.LaxMonoidal.ε L ≫ L.map (ringOne R)) ≫ eR.inv =
          ringOne A := IsMonHom.one_hom eR.inv
      rw [← Category.assoc, hu]
      have ht : Functor.LaxMonoidal.ε L ≫
          CartesianMonoidalCategory.terminalComparison L = 𝟙 _ :=
        CartesianMonoidalCategory.toUnit_unique _ _
      rw [← Category.assoc, ht, Category.id_comp]
    · apply adjunct_binary L V adj _ _ (ringMul R) (ringMul A) eR.inv
      exact binary_inverse L _ _ eR _ _ hm
  let P := imageFunctor V A R d haP hmP
  refine ⟨P, imageFunctorUnderlying V A R d haP hmP, ?_⟩
  intro H
  constructor
  · change fromProd _ _ ≫ addition R (imageModule V A R d haP hmP H) ≫ 𝟙 _ =
      prod.map (𝟙 _) (𝟙 _) ≫ inv (prodComparison V _ _) ≫
        V.map (fromProd _ _ ≫ addition A H)
    simp only [prod.map_id_id, Category.comp_id, Category.id_comp]
    rw [imageModule_addition_comparison V A R d haP hmP H]
    set_option backward.isDefEq.respectTransparency false in
      simp only [IsIso.inv_hom_id_assoc]
    rfl
  · exact imageModule_action_comparison_right V A R d haP hmP H

end CochainGeometricConstruction

set_option backward.isDefEq.respectTransparency false
end SheafOfModules

namespace SheafOfModules.CochainScalarConstruction
open scoped TensorProduct ChangeOfRings
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
private abbrev ringSheaf {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private noncomputable abbrev underlying {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  toSheaf (ringSheaf R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})

section Pure
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u})

/-- The image of a sectionwise pure tensor in the sheaf tensor.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
private noncomputable def pure (M N : SheafOfModules.{u} (ringSheaf R))
    (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory R).tensorObj M N).val.obj W :=
  (tensorObjIsoSheafification M N).inv.val.app W
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
      (M.val ⊗ N.val)).app W (m ⊗ₜ[R.obj.obj W] n))

/-- A map from a tensor is determined by pure sections. Source: Stacks 03EK
(auxiliary; not a blueprint node).
Proof: use the module sheafification adjunction, then sectionwise tensor generation. -/
private theorem pure_hom_ext (M N H : SheafOfModules.{u} (ringSheaf R))
    {f g : (monoidalCategory R).tensorObj M N ⟶ H}
    (h : ∀ W m n, f.val.app W (pure R M N W m n) =
      g.val.app W (pure R M N W m n)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)
  apply (cancel_epi (tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact h W m n

end Pure
/-- Existence part of the sheaf tensor universal property.
(auxiliary; not a blueprint node)
The sectionwise tensor maps are assembled into a presheaf morphism and uniquely factored
through module sheafification; this is exactly the existence construction in the source proof. -/
private theorem tensor_bilinear_exists {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (F G H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (β : ∀ U : Cᵒᵖ,
      F.val.obj U →ₗ[R.obj.obj U] G.val.obj U →ₗ[R.obj.obj U] H.val.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : F.val.obj U) (y : G.val.obj U),
      β V (F.val.map f x) (G.val.map f y) = H.val.map f (β U x y)) :
    ∃ φ : (monoidalCategory R).tensorObj F G ⟶ H, ∀ (U : Cᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      φ.val.app U ((tensorObjIsoSheafification.{vC, uC, u} F G).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{u, vC, u, uC}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.app
            (F.val ⊗ G.val)).app U (x ⊗ₜ[R.obj.obj U] y))) = β U x y := by
  let := monoidalCategory R
  let q : F.val ⊗ G.val ⟶ H.val :=
    { app := fun U ↦ ModuleCat.ofHom (X := (F.val ⊗ G.val).obj U)
        (Y := H.val.obj U) (TensorProduct.lift (β U))
      naturality := by
        intro U V f
        ext t
        change TensorProduct.lift (β V) ((F.val ⊗ G.val).map f t) =
          H.val.map f (TensorProduct.lift (β U) t)
        induction t using TensorProduct.inductionOn with
        | tmul x y =>
          change β V (F.val.map f x) (G.val.map f y) = H.val.map f (β U x y)
          exact hβ f x y
        | add t s ht hs => simp only [map_add, ht, hs] }
  let adj := PresheafOfModules.sheafificationAdjunction.{u, vC, u, uC}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
  let a := (adj.homEquiv (F.val ⊗ G.val) H).symm q
  refine ⟨(tensorObjIsoSheafification.{vC, uC, u} F G).hom ≫ a, ?_⟩
  intro U x y
  have h := (adj.homEquiv (F.val ⊗ G.val) H).apply_symm_apply q
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun t ↦ (t.app U) (x ⊗ₜ[R.obj.obj U] y)) h
  change a.val.app U (((adj.unit.app (F.val ⊗ G.val)).app U)
    (x ⊗ₜ[R.obj.obj U] y)) = β U x y at hh
  change a.val.app U ((tensorObjIsoSheafification.{vC, uC, u} F G).hom.val.app U
    ((tensorObjIsoSheafification.{vC, uC, u} F G).inv.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) (x ⊗ₜ[R.obj.obj U] y)))) = _
  have hi := congrArg (fun t : (PresheafOfModules.sheafification.{u, vC, u, uC}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).obj
        (F.val ⊗ G.val) ⟶ _ ↦ t.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) (x ⊗ₜ[R.obj.obj U] y)))
    (tensorObjIsoSheafification.{vC, uC, u} F G).inv_hom_id
  change (tensorObjIsoSheafification.{vC, uC, u} F G).hom.val.app U
    ((tensorObjIsoSheafification.{vC, uC, u} F G).inv.val.app U
      (((adj.unit.app (F.val ⊗ G.val)).app U) (x ⊗ₜ[R.obj.obj U] y))) = _ at hi
  rw [hi]
  exact hh

private theorem cochain_tensor_bilinear_universal
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (F G H : SheafOfModules.{u} (ringSheaf R))
    (β : ∀ W : Cᵒᵖ,
      F.val.obj W →ₗ[R.obj.obj W] G.val.obj W →ₗ[R.obj.obj W] H.val.obj W)
    (hβ : ∀ {W V : Cᵒᵖ} (i : W ⟶ V) (x : F.val.obj W) (y : G.val.obj W),
      β V (F.val.map i x) (G.val.map i y) = H.val.map i (β W x y)) :
    ∃! φ : (monoidalCategory R).tensorObj F G ⟶ H,
      ∀ W x y, φ.val.app W (pure R F G W x y) = β W x y := by
  obtain ⟨φ, hφ⟩ := tensor_bilinear_exists R F G H β hβ
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply pure_hom_ext R F G H
  intro W x y
  exact (hψ W x y).trans (hφ W x y).symm

end SheafOfModules.CochainScalarConstruction

namespace SheafOfModules.CochainInversePairing
open SheafOfModules.CochainGeometricConstruction SheafOfModules.GeometricConstruction
open SheafOfModules.CochainScalarConstruction
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

private theorem binary_of_graph
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    {X Y Z : Sheaf J (Type u)} {A B E : Sheaf K (Type u)}
    (dX : F.obj X ⟶ A) (dY : F.obj Y ⟶ B) (dZ : F.obj Z ⟶ E)
    (a : X ⨯ Y ⟶ Z) (b : A ⨯ B ⟶ E)
    (op : ∀ U, X.obj.obj U → Y.obj.obj U → Z.obj.obj U)
    (op' : ∀ V, A.obj.obj V → B.obj.obj V → E.obj.obj V)
    (hs : ∀ U p, a.hom.app U p =
      op U ((prod.fst : X ⨯ Y ⟶ X).hom.app U p)
        ((prod.snd : X ⨯ Y ⟶ Y).hom.app U p))
    (ht : ∀ V p, b.hom.app V p =
      op' V ((prod.fst : A ⨯ B ⟶ A).hom.app V p)
        ((prod.snd : A ⨯ B ⟶ B).hom.app V p))
    (hgraph : ∀ (T : Sheaf J (Type u)) (x : T ⟶ X) (y : T ⟶ Y) (z : T ⟶ Z),
      (∀ U p, z.hom.app U p = op U (x.hom.app U p) (y.hom.app U p)) →
      ∀ V p, (F.map z ≫ dZ).hom.app V p =
        op' V ((F.map x ≫ dX).hom.app V p) ((F.map y ≫ dY).hom.app V p)) :
    F.map a ≫ dZ = prodComparison F X Y ≫ prod.map dX dY ≫ b := by
  have h₁ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.fst =
      F.map prod.fst ≫ dX := by simp only [prod.map_fst, prodComparison_fst_assoc]
  have h₂ : prodComparison F X Y ≫ prod.map dX dY ≫ prod.snd =
      F.map prod.snd ≫ dY := by simp only [prod.map_snd, prodComparison_snd_assoc]
  ext V p
  have h := hgraph (X ⨯ Y) prod.fst prod.snd a hs V p
  change (F.map a ≫ dZ).hom.app V p = b.hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p)
  rw [ht]
  have hh₁ := congrArg (fun k ↦ k.hom.app V p) h₁
  have hh₂ := congrArg (fun k ↦ k.hom.app V p) h₂
  change (prod.fst : A ⨯ B ⟶ A).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₁
  change (prod.snd : A ⨯ B ⟶ B).hom.app V
    ((prodComparison F X Y ≫ prod.map dX dY).hom.app V p) = _ at hh₂
  rw [hh₁, hh₂]
  exact h

private noncomputable def radd
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) := fromProd (rset R) (rset R) ≫ ringAdd R

private noncomputable def rmul
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) := fromProd (rset R) (rset R) ≫ ringMul R

private noncomputable def madd
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (base R)) :=
  fromProd ((mset R).obj M) ((mset R).obj M) ≫ addition R M
private noncomputable def msmul
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (base R)) :=
  fromProd (rset R) ((mset R).obj M) ≫ action R M

set_option backward.isDefEq.respectTransparency false in
private theorem madd_spec
    {E : Type uE} [Category.{vE} E] [EssentiallySmall.{u} E]
    {T : GrothendieckTopology E}
    [T.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (A : Sheaf T CommRingCat.{u}) (H : SheafOfModules.{u} (base A)) :
    addSpec H (madd A H) := by
  intro W x
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem msmul_spec
    {E : Type uE} [Category.{vE} E] [EssentiallySmall.{u} E]
    {T : GrothendieckTopology E}
    [T.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (A : Sheaf T CommRingCat.{u}) (H : SheafOfModules.{u} (base A)) :
    smulSpec H (msmul A H) := by
  intro W x
  rfl

variable (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
  (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (V : Sheaf K (Type u) ⥤ Sheaf J (Type u))
  (adj : F ⊣ V) [PreservesFiniteLimits F]
  (I : AlgebraicInverseImage F R RI)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem ringOperations :
    F.map (radd R) = prodComparison F (rset R) (rset R) ≫
        prod.map I.ringUnderlying.hom I.ringUnderlying.hom ≫ radd RI ≫
          I.ringUnderlying.inv ∧
    F.map (rmul R) = prodComparison F (rset R) (rset R) ≫
        prod.map I.ringUnderlying.hom I.ringUnderlying.hom ≫ rmul RI ≫
          I.ringUnderlying.inv := by
  constructor
  · apply (cancel_mono I.ringUnderlying.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact binary_of_graph F I.ringUnderlying.hom I.ringUnderlying.hom
      I.ringUnderlying.hom (radd R) (radd RI)
      (fun U x y ↦ @Add.add (R.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add (RI.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun T x y z hz U t ↦ I.ringAdd T x y z hz U t)
  · apply (cancel_mono I.ringUnderlying.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact binary_of_graph F I.ringUnderlying.hom I.ringUnderlying.hom
      I.ringUnderlying.hom (rmul R) (rmul RI)
      (fun U x y ↦ @Mul.mul (R.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Mul.mul (RI.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun T x y z hz U t ↦ I.ringMul T x y z hz U t)

variable [PreservesFiniteLimits V]

attribute [local irreducible] CochainScalarConstruction.pure

-- The tensor construction is already locally irreducible.

end SheafOfModules.CochainInversePairing

namespace SheafOfModules.CochainInversePairing
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
open SheafOfModules.CochainScalarConstruction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
  (uInv : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (I : AlgebraicInverseImage uInv R RI)

set_option quotPrecheck false
set_option hygiene false in
local notation "𝓡" R =>
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj R
set_option hygiene false in
local notation "𝓤" R =>
  (toSheaf (𝓡 R) ⋙ sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u}))

end SheafOfModules.CochainInversePairing
