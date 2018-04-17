cp $1 x.ba
cp $2 y.ba
java -jar toTimbuk.jar x.ba
java -jar toTimbuk.jar y.ba
./vata incl x.ba.timbuk y.ba.timbuk
rm x.ba.timbuk
rm y.ba.timbuk
rm x.ba
rm y.ba
