<?php
header('Content-Type: application/json');

$n= isset($_GET['n'])?$_GET['n']:0;
if($n===6){echo "BOAIJSIOJOIDSF:  CONGRATUATLIONS!!!! YOU WON1!!";}

//echo "This is tab #".$n."<br>";
//$c=["oisdjfodi","iodsfoia","iwodjvoasv","diosjoifsoid","disofjosdfij"];
//if(isset($c[$n]))
echo json_encode(["CONTENT"=>"TAB NUMBER $n"]);
?>