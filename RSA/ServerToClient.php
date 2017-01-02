<?php
$C_pub=isset($_GET['pub'])?$_GET['pub']:null;
$str=isset($_GET['str'])?$_GET['str']:null;
$size=isset($_GET['size'])?intval($_GET['size']):die;
if(!in_array($size,[512,1024,2048,4096]))die;

set_time_limit(0);

$cypher="";
session_start();

if(empty($_SESSION['PUBLIC_'.$size])){
$config = array(
    "digest_alg" => "sha512",
    "private_key_bits" => $size,
    "private_key_type" => OPENSSL_KEYTYPE_RSA,
);
    
$res = openssl_pkey_new($config);

openssl_pkey_export($res, $S_priv);
$S_pub = openssl_pkey_get_details($res)['key'];

$_SESSION['PUBLIC_'.$size]=$S_pub;
$_SESSION['PRIVATE_'.$size]=$S_priv;

if(isset($C_pub)&&isset($str)){ openssl_public_encrypt($str, $cypher, $C_pub);$cypher = base64_encode($cypher);}

}

$Output=array(
	"CYPHER"=>$cypher,
	"PUBLIC_$size"=>$_SESSION['PUBLIC_'.$size],
);

echo json_encode($Output);
?>