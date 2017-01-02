<?php
$cypher=isset($_GET['cyph'])?$_GET['cyph']:die;
$size=isset($_GET['size'])?intval($_GET['size']):die;
if(!in_array($size,[512,1024,2048,4096]))die;

session_start();
openssl_private_decrypt(base64_decode($cypher), $decypher, $_SESSION['PRIVATE_'.$size]);

$Output=array(
	"DECYPHER"=>$decypher
);

session_destroy();

echo json_encode($Output);
?>