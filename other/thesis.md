# A könnyűzene formális modellje

## Abstract
A zenei jelfeldolgozással foglalkozó algoritmusok gyakran figyelmen kívül hagyják magának a zenének az elméletét. Ennek oka a formális zenei modell hiánya. A munkámban megmutatom, hogy a formalizált zeneelmélet felhasználható a jelfeldolgozási kimenetek gépi elbírálásában. Megvizsgálom, hogy a zenei modell megválasztása hogyan befolyásolja a feldolgozás egyes szintjeit, hogyan lehet segítségükre, és hogyan verifikálhatóak számítógéppel az eredményeik. Arra is kitérek, hogy ez a számítási zenetudományi feladat milyen szoftvertechnológiai kihívásokkal jár, és azok hogyan oldhatóak meg.  






## A kutatási célok meghatározása

A kutatás legfőbb célja megállapítani, hogy milyen eszközökkel lehetséges a zene modelljét formalizálni oly módon, hogy a kész modell könnyen beágyazható legyen zenei jelfeldolgozási feladatokba. Ennek hasznossága illetve szükségessége több szinten megnyilvánul valós projektekben.

[zenei modell szintjei kép: 1. követelmények, dokumentációk 2. reprezentálás 3. zeneelméleti definíciók, függvények 4. zenei kiértékelés]

 A zenei modell hiánya legalacsonyabb szinten a feladat megfoglamazásánál, a követelmények egyértelmű definiálásánál jelentkezik. A zenei projektekre jellemző, hogy mivel leggyakrabban zenei háttértudással rendelkező fejlesztők készítik azokat, a zenészek által ismert zeneelmélet mentén fogalmaznak, ezek  viszont gyakran pontatlanok tudnak lenni a különböző zenei stílusok különböző fogalmazásai miatt. Ezen felül a művészet központú zeneelmélet nem tekinti céljának a formalizáltságot, sőt több esetben is hagyomány alapján hoz meg döntéseket. Ezektől mind eltekintve is nehezen található olyan zeneelméleti összefoglaló, ami a hanghullámoktól a zenei formáig és stílusokig mindent logikusan felépítve tárgyal, így tehát általánosságban rossz gyakorlat a művészeti zeneelmélet használata követelmények megfogalmazásánál.

[Kép béna zenei dokumentációról]
[Példa ellentmondó zeneelmélet könyvekből (konszonancia)]

A modell szerepe a zenei adatok tárolásában is megjelenik. Dalok reprezentálására két módszert használnak a gyakorlatban. Az egyik a hangok MIDI fájlként való tárolása. Ennek egyértelmű hátránya, hogy a ritmikai információ kinyerése feldolgozást igényel. Ennek oka, hogy a hangok kezdete és vége van csak eltárolva, a hangérték megállíptása pedig sok esetben nem egyértelmű ezek alapján. Minden hanghoz a hang magasságán kívűl még a hang erősségének értéke van feljegyezve. Ennek a számnak az interpretálása szintén nem egyértelmű, hiszen egyszerre fejezi ki a hangszer hangerejét, a hang dinamikáját, a dal adott részének a dinamikáját illetve akár a hang ütemben kapott szerepét is. Ezen indokok miatt a MIDI formátum bár a zene fizikai leírásának megfelelő reprezentáció tud lenni, sok esetben további feldolgozást igényel, így általánosságban véve nem tekinthető magasszintű zenei jelfeldolgozási feladatoknál megfelelő kimeneti formátumnak.

[MIDI példa, esetleg valami nem egyértelmű ritmikai dologról]

A zeneművek másik reprezentálási formája jellemzően valamilyen kottaszerű ábrázolást jelent. Bár ezen a területen megvalósítás és célkitűzések szempontjából széles skálán mozognak az eszközök, gyakori probléma viszont a jelfeldolgozáshoz való használatukban, hogy nem magát a zenét, hanem a kottát reprezentálják, ez pedig azon felül, hogy szükségtelen komplikációkat okoz, több esetben félrevezeti a fejlesztőket az eredmények értékelésénél, vagy a célok meghatározásában. Erre példaként hozható az ütemmutató és az ütemen belüli hangsúlyozás feljegyzése. Mivel az ütemmutató meghatározza, hogy az adott ütemen belül mely hangokra kerül nagyobb hangsúly, ezeken a hangokon kottában a megfelelő hangsúlyozást külön jelölni felesleges, viszont jelfeldolgozási feladatoknál minden egyes hang pontos hangsúlyozását elhagyni nagymértékű adatkiesést jelentene és nagyban megnehezítené a további feldolgozást. Ezen kívűl a kottába feljegyezhető dinamikai kifejezések gépi értelmezése lehetetlen vállalkozás lenne, ezek nélkül viszont nem megfelelő a zene reprezentálása kottában, így a kotta bár megfelelő végkimeneti formátum magasszintű jelfeldolgozási feladatoknak, a feladat végrehajtása közben viszont rossz gyakorlat a használata. Fontos megjegyezni, hogy léteznek olyan kottaszerű reprezentáló eszközök, amelyek jól kezelnek a most említett nehézségek közül többet is.

[Kotta példa]
[Music21 nem is olyan rossz példa]
[reprezentálás szintjei: alul MIDI felül kotta középen hiányzik a megfelelő eszköz]

Egy általános zenei modellre a jelfeldolgozás során mint függvény gyűjteményre is szükség van. Erre a problémára számos zeneelmélet könyvtár létezik, viszont ezek saját típusokat használnak, amik nehezen kapcsolódnak zenei reprezentációs eszközökhöz. Másik általános hiányosságuk, hogy a fizikai zeneelmélet definícióit nem tartalmazzák.

[Music21 voicing dolog hogy viszonyul egy többszólamú rész reprezentálásához MIDI-ben?]

Legmagasabb szinten pedig a zene formális modellje használható lenne jelfeldolgozó algoritmusok kimenetének zenei kiértékelésére. Bár ez használat szempontjából nem különül el a korábban említett zeneelmélet könyvtár eszközöktől, abból a szempontból fontos elkülöníteni mégis, hogy ez a feladat sokkal magasabb szintű zenei formalizálást igényel. Példaként hozható egy dal részeinek megnevezése, vagy műfajának felismerése.

[Ide is valami]


A modell formalizálásnak eszközének megválasztásán kívül megvizsgálom, azt is, hogy melyek azok a zeneelméleti területek illetve konkrét feladatok amelyeket egy ilyen modellnek tárgyalnia kell annak érdekében, hogy mai jelfeldolgozási feladatokat megfelelően tudjon támogatni. Az elmúlt évtizedekben a számítási zenetudomány leginkább klasszikus zene köré épített elemzéseket, melyek sokszor könnyűzenére nem értelmezhetőek, illetve az könnyűzenére átültethető analízisek közül is kevés olyan akad, aminek gyakorlati haszna lenne egy tipikus mai projektben. Az elmúlt években robbanásszerűen növekedett a zenei jelfeldolgozás alkalmazása. Megjelent a streaming szolgáltatóknál és a zenei megosztó felületeken is, megbízható működésüknek szükségét pedig mi sem fejezné ki jobban, mint hogy eredményeik gyakran jogi következményeket vonnak maguk után. A futurisztikusnak tűnő okoserősítőkben pedig nem ritka funkció már a virtuális zenekar, amely minden instrukció nélkül real time kíséri a játékost a dalban, vagy akár együtt improvizál vele. Egy ilyen eszköz korábban nem látott feladatok merülnek fel. 

Vizsgálni fogom a zenei analízis alapvető kérdését, a zene és nem zene elválasztását. Minél szigorúbb állításokkal fogom szűkíteni a könnyűzene fogalmát és tanulmányozni fogom ennek a szigorításnak a jelentősségét. Kitérek az ütem és az ehhez tartozó fogalmak jelentésére, különböző definiálási lehetőségeire és az ezekhez tartozó ütemmutató felismerésének lehetséges megvalósításaira. Végül pedig megvizsgálom, hogy milyen fogalmak mentén definiálható a zenei variáció és a variáció mentén hogyan adható meg egy dal felépítése és részeinek kapcsolata.


 - zeneelmélet formális alapjait lerakni



## A problémakör irodalmának, az előzményének rövid áttekintése

 - nincs hiány az analízisekből, összefoglaló
 - szinte kizárólag klasszikus zenére épülő kutatások vannak
 - dolgok összevissza vannak, nincs kipróbálható algoritmus és eszköz sem
 
konszonancia https://www.jstor.org/stable/40285261?seq=1
http://gttm.jp/hamanaka/wp-content/uploads/2015/12/ISMIR2007Tutorial_Slide.pdf
https://www.jstor.org/stable/900759



## A téma feldolgozás során alkalmazott módszerek

### Az eszköz megválasztásáról
 - Coq, Agda
 - Mivel másabb, mint mondjuk egy python package







## A téma feldolgozásának részletezése, részletes ismertetése

 - a modell szintjein végigmenni
 - követelményeknél nem lehet egy az egybe a coqot használni, de coqban le lehet írni állításokatt a zenei kifejezésekre, ezekre lehet hivatkozni a követelményekben.

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


## gondolkozok

variáció eszközei:
 - transzponálás
 - elnyújtás
 - díszítás
 - egyszerűsítés
 - harmónia helyettesítés 
 - Refrént már azelőtt érezzük, hogy elkezdődne  
 - A és B elkülönítése több lépésben. Addig csökken a lehetséges különbség értéke, amíg fel nem ismerődik a két különböző rész.
