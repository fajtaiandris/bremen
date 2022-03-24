# A könnyűzene formális modellje

## Abstract
A zenei jelfeldolgozással foglalkozó algoritmusok gyakran figyelmen kívül hagyják magának a zenének az elméletét. Ennek oka a formális zenei modell hiánya. A munkámban megmutatom, hogy a formalizált zeneelmélet felhasználható a jelfeldolgozási kimenetek gépi elbírálásában. Megvizsgálom, hogy a zenei modell megválasztása hogyan befolyásolja a feldolgozás egyes szintjeit, hogyan lehet segítségükre, és hogyan verifikálhatóak számítógéppel az eredményeik. Arra is kitérek, hogy ez a számítási zenetudományi feladat milyen szoftvertechnológiai kihívásokkal jár, és azok hogyan oldhatóak meg.  






## A kutatási célok meghatározása

 - mennyit segít, ha erős feltevéseket teszek a zenére, mivel tudom, hogy pop





## A problémakör irodalmának, az előzményének rövid áttekintése

 - szinte kizárólag klasszikus zenére épülő kutatások vannak
 - dolgok összevissza vannak, nincs kipróbálható algoritmus és eszköz sem
http://gttm.jp/hamanaka/wp-content/uploads/2015/12/ISMIR2007Tutorial_Slide.pdf
https://www.jstor.org/stable/900759



## A téma feldolgozás során alkalmazott módszerek

### Az eszköz megválasztásáról
 - Coq, Agda
 - Mivel másabb, mint mondjuk egy python package







## A téma feldolgozásának részletezése, részletes ismertetése

### A zenei hang formalizálásáról
 - A zenei hang szintjei
 - Más eszközök hogyan formalizálják
 - szintaktikai cukrok
 - állítások, bizonyítások
 - példa, hogy máshol ezt rosszul csinálták (az én modellem szerint)

### A ritmus formalizálásáról
 - division és duration formalizálása (nem túl izgalmas)
 - az ütemmutató nem része a zenének, de megállapítható róla
 - példa: egy ütemmutató algoritmus kiértékel egy hangfájlt, én pedig a modellemmel a hangfájl leiratának birtokában megmondom, hogy jó-e. Végülis egy bizonyítás, de igazán csak egy unit teszt.

### A zenei struktúra formalizálásáról
 - dallam
 - többszólamú zene lehetséges formalizálásai
 - variáció definiálása
 - a zene részeinek elkülönítése
 
### A modell beágyazása projektekbe
 - példa paraméterezhető automatikus bizonyításra, amit egy másik program használni tud
 - a modellt lehet végülis szintetizálásra használni, így könnyen előállíthatók algoritmusoknak teszt esetek, amiket könnyű vizsgálni









## Az eredmények összefoglaló értékelése és a levonható következtetések








## Belefoglalni
 - megírom coq a zeneelméletet   
 - veszek egy algoritmust ami állít valamit valamilyen zenéről, ezt agdával bebizonyítom   
 - tehát vannak különbözőek. Például egy másik modell lenne, ha zenei hangok csak számok lennének.   
 - frekvencia szinten mik állapíthatóek meg, hang szinten, teljes egészében véve   
 - tehát mutatok arra példát, hogy valahogy visszacsatolni a részeredményt, hogy finomuljon az algoritmus   
 - tudok-e valami olyat írni, ami automatikusan bizonyít egy parametizálható állítást (pl. ez a dallam F dúrból C-be majd vissza F-be vált)   
 - Lehet-e ezt végül coq csinálni? Lassú lesz? hogyan integrálom? Esetleg megírom pythonban is és összehasonlítom.   
 - Keresek valami zenei algoritmust, amit be tudok bizonyítani, hogy hibásan működik
 - Refrént már azelőtt érezzük, hogy elkezdődne  
 - A és B elkülönítése több lépésben. Addig csökken a lehetséges különbség értéke, amíg fel nem ismerődik a két különböző rész.


## gondolkozok

variáció eszközei:
 - transzponálás
 - elnyújtás
 - díszítás
 - egyszerűsítés
 - harmónia helyettesítés 
